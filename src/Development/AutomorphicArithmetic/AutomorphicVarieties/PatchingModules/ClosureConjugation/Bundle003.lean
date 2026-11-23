module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle001
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle002

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.pair_mf :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (l : B) ∈ maximalIdeal B ∧ ∃ (h : ℕ) (χ : Fin n → F.G₀ →* (ResidueField B)ˣ), u.D.map (residue B) = GDet.ofChars χ ∧ MultFree χ h := by
  intro l _ F n O _ _ _ hc _ r B _ _ _ u hΦ
  haveI := hc.finite
  haveI := hc.char
  let e : ResidueField O ≃+* ResidueField B := RingEquiv.ofBijective _ (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI hch : CharP (ResidueField B) l := charP_of_injective_ringHom (f := e.toRingHom) e.injective l
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.1 (F.η.ker.isClosed_of_isOpen F.η_open).isCompact
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ := fun i => pushCh e.toRingHom (r.chib i)
  have hU : Function.Injective (Units.map (e.toRingHom : ResidueField O →* ResidueField B)) :=
    Units.map_injective e.injective
  have hop : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    have : (χ i).ker = (r.chib i).ker := MonoidHom.ker_comp_of_injective _ _ hU
    rw [this]
    exact r.chib_open i
  have hinj : Function.Injective χ := fun i j hij =>
    r.chib_inj (MonoidHom.ext fun g => hU (DFunLike.congr_fun hij g))
  obtain ⟨h, hh⟩ := exists_multFree_of_phiCond_of_injective_chars l χ hΦ hop hinj
  refine ⟨hfin, ?_, h, χ, ?_, hh⟩
  · rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  · have h1 : residue B = e.toRingHom.comp (res O B : B →+* ResidueField O) :=
      RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
    rw [h1, ← (d_gmap u.D).2.1, u.red, Resid.Dbar, (d_gmap r.Dbar).2.2.2]
    unfold GDet.ofChars
    congr 1
    refine MonoidHom.ext fun g => ?_
    change (Matrix.diagonal fun i => ((r.chib i g : (ResidueField O)ˣ) : ResidueField O)).map e.toRingHom = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.eps_eq :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), ∀ g : G.G₀, P.f (G.frame.eps O B g : Bˣ) = ((G0.frame.eps ℤ_[l] x.A (h.p₀ g) : x.Aˣ) : x.A) ∧ h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P g
  have hl : (l : x.K) = 0 := by
    by_contra hn
    obtain ⟨p, hp⟩ := CharP.exists x.K
    have hpp : p.Prime := CharP.char_is_prime x.K p
    have hne : p ≠ l := by rintro rfl; exact hn (CharP.cast_eq_zero _ _)
    have h6 : IsUnit ((p : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hne ?_)
      rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
      exact ((Nat.prime_dvd_prime_iff_eq Fact.out hpp).1 (by exact_mod_cast hlt)).symm
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_intCast, Int.cast_natCast, CharP.cast_eq_zero] at h8
    exact not_isUnit_zero h8
  have hA : (l : x.A) = 0 := by rw [← map_natCast (PowerSeries.C (R := x.K)), hl, map_zero]
  have key : ∀ φ : ℤ_[l] →+* x.A, ∀ a, φ a = (a.zmodRepr : x.A) := fun φ a => by
    have h1 := PadicInt.sub_zmodRepr_mem a
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := congrArg φ hc
    rw [map_mul, map_natCast, hA, mul_zero, map_sub, map_natCast] at h2
    exact sub_eq_zero.1 h2.symm
  refine ⟨?_, Subtype.ext ?_⟩
  · have e1 := key (P.f.toRingHom.comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))) (G.ε g : ℤ_[l])
    have e2 := key ((algebraMap ℤ_[l] x.A).comp (algebraMap ℤ_[l] ℤ_[l])) (G0.ε (h.p g) : ℤ_[l])
    rw [h.ε] at e2
    refine e1.trans (e2.symm.trans ?_)
    rw [← h.ε]; rfl
  · show h.p (G.c * g * G.c⁻¹) = G0.c * h.p g * G0.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c]
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.f_surj :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} (P : OoPt h x u), Function.Surjective P.f ∧ IsLocalHom P.f.toRingHom := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P
  have hK : IsCO O x.K := by
    refine IsCO.mk ?_ ?_ ?_
    · rw [IsLocalRing.maximalIdeal_eq_bot]
      infer_instance
    · constructor
      intro a ha
      by_contra hna
      have hm : a ∈ maximalIdeal O := hna
      have hker : RingHom.ker (algebraMap O x.K) = maximalIdeal O :=
        eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ P.surj)
      have h0 : algebraMap O x.K a = 0 := by
        rw [← RingHom.mem_ker, hker]
        exact hm
      rw [h0] at ha
      exact not_isUnit_zero ha
    · intro y
      obtain ⟨a, rfl⟩ := P.surj y
      exact ⟨a, by rw [sub_self]; exact Ideal.zero_mem _⟩
  have hA : IsCO O x.A := co_mvps O x.K Unit
  have hs : P.s ∈ maximalIdeal B := by
    rw [← res_eq_zero_iff O B, ← res_map P.f, P.f_s, res_eq_zero_iff,
      PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl
  have hsurj : Function.Surjective P.f := by
    apply co_surj O B x.A P.f
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hm := Ideal.mem_map_of_mem P.f hs
    rw [P.f_s] at hm
    exact Ideal.mem_sup_left hm
  exact ⟨hsurj, IsLocalHom.of_surjective P.f.toRingHom hsurj⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

private theorem span_of_gram {n : ℕ} {K : Type} [Field K] (s : Set (Matrix (Fin n) (Fin n) K))
    (x y : Fin (n * n) → Matrix (Fin n) (Fin n) K) (hx : ∀ a, x a ∈ s)
    (hdet : Matrix.det (Matrix.of fun a b => (x a * y b).trace) ≠ 0) : Submodule.span K s = ⊤ := by
  have hrank : Module.finrank K (Matrix (Fin n) (Fin n) K) = Fintype.card (Fin (n * n)) := by
    simp [Module.finrank_matrix]
  have hli : LinearIndependent K x := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have : g = 0 := by
      apply Matrix.eq_zero_of_vecMul_eq_zero hdet
      funext c
      have hvec : Matrix.vecMul g (Matrix.of fun a b => (x a * y b).trace) c
          = ((∑ a, g a • x a) * y c).trace := by
        simp [Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.trace_sum]
      rw [hvec, hg]
      simp
    intro i
    simp [this]
  have := hli.span_eq_top_of_card_eq_finrank' hrank.symm
  rw [eq_top_iff, ← this]
  apply Submodule.span_mono
  rintro _ ⟨a, rfl⟩
  exact hx a

private theorem discSt_iff {n : ℕ} {A G K : Type} [CommRing A] [Group G] [Field K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ)
    (Q : Ideal A) (hQ : ∀ b, f b = 0 ↔ b ∈ Q) :
    DiscSt D Q ↔ Submodule.span K (Set.range ρ) = ⊤ := by
  have key : ∀ g g' : Fin (n * n) → G,
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (g a * g' b) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g' b)).trace) := by
    intro g g'
    rw [RingHom.map_det]
    congr 1
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.of_apply,
      tr_of_map hn D f ρ h, map_mul]
  constructor
  · rintro ⟨g, g', hg⟩
    refine span_of_gram _ (fun a => ρ (g a)) (fun a => ρ (g' a)) (fun a => ⟨_, rfl⟩) fun h0 => hg ?_
    rw [← hQ, key]
    exact h0
  · intro hs
    obtain ⟨x, hx, hdet⟩ := (g_gram _ _ _).1 hs
    choose g hg using hx
    refine ⟨fun a => g (finProdFinEquiv.symm a), fun a => g (finProdFinEquiv.symm a), fun hm => hdet ?_⟩
    rw [← hQ, key] at hm
    rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← hm]
    congr 1
    ext a b
    simp only [hg, Matrix.submatrix_apply, Matrix.of_apply]

private theorem top_of_single {n : ℕ} {K : Type} [Field K] (S : Submodule K (Matrix (Fin n) (Fin n) K))
    (h : ∀ i j, ∃ c : K, c ≠ 0 ∧ Matrix.single i j c ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  obtain ⟨c, hc, hm⟩ := h i j
  have := S.smul_mem (M i j * c⁻¹) hm
  rwa [Matrix.smul_single, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one] at this

private theorem single_mem_blk {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {n a : ℕ}
    (V₁ V₂ : Submodule A R) (i j : Fin n) (c : R)
    (h1 : (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₁) (h2 : ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → c ∈ V₂) :
    Matrix.single i j c ∈ blkMat n a V₁ V₂ := by
  intro i' j'
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    rw [Matrix.single_apply_same]
    exact ⟨h1, h2⟩
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ hij]
    exact ⟨fun _ => V₁.zero_mem, fun _ => V₂.zero_mem⟩

theorem UpperTheory.V.Pa.urep_stable :
    ∀ {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} {h : G.Hom G0} {n : ℕ} {x : NP G0.frame n} {B : Type} [CommRing B] [IsLocalRing B] {D : GDet n B G.G₀} {I : Set (MonoidAlgebra B G.G₀)} {Bh : Type} [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh] {rF : Bh →+* FractionRing x.A} {e : G.G₀ →* Bˣ} (V : URep h x D I Bh rF e), ∀ Q : Ideal Bh, Q.IsPrime → (DiscSt (D.map (algebraMap B Bh)) Q ↔ x.a = n ∨ ∃ y ∈ V.N, ∃ z ∈ V.N, ∃ b : Bh, b ∉ Q ∧ y * z = algebraMap Bh V.AA b) := by
  intro l _ L G G0 h n x B _ _ D I Bh _ _ _ rF e V Q hQp
  haveI := V.fin
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  obtain ⟨Q', -, hQ', hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := V.AA) Q ⊥ (by
    intro b hb
    have : b = 0 := V.inj (by simpa using hb)
    rw [this]; exact Q.zero_mem)
  let f : V.AA →+* Q'.ResidueField := algebraMap _ _
  have hf : ∀ b, (f.comp (algebraMap Bh V.AA)) b = 0 ↔ b ∈ Q := fun b => by
    rw [RingHom.comp_apply, Ideal.algebraMap_residueField_eq_zero, ← hc, Ideal.mem_comap]
  let ρ : G.G₀ →* Matrix (Fin n) (Fin n) Q'.ResidueField := f.mapMatrix.toMonoidHom.comp V.vr
  have hρ : (D.map (algebraMap B Bh)).map (f.comp (algebraMap Bh V.AA)) = GDet.ofRep ρ := by
    rw [(d_gmap D).2.1, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← (d_gmap D).2.1, V.det]
    exact (d_gmap (GDet.ofRep V.vr)).2.2.2 f V.vr
  rw [discSt_iff hn _ _ ρ hρ Q hf]
  have hmem : ∀ Y ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N,
      Y.map f ∈ Submodule.span Q'.ResidueField (Set.range ρ) := by
    intro Y hY
    rw [← V.span] at hY
    induction hY using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨g, rfl⟩ := hy
      exact Submodule.subset_span ⟨g, rfl⟩
    | zero => rw [Matrix.map_zero _ (map_zero f)]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Matrix.map_add _ (map_add f)]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha =>
      have : (c • a).map f = f (algebraMap Bh V.AA c) • a.map f := by
        ext i j
        rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Algebra.smul_def, map_mul, smul_eq_mul]
      rw [this]
      exact Submodule.smul_mem _ _ ha
  have hone : (1 : V.AA) ∈ (1 : Submodule Bh V.AA) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hsing : ∀ (i j : Fin n) (c : V.AA), (Matrix.single i j c).map f = Matrix.single i j (f c) :=
    fun i j c => Matrix.map_single i j c f
  constructor
  · intro hs
    by_cases ha : x.a = n
    · exact Or.inl ha
    right
    have hlt : x.a < n := lt_of_le_of_ne x.a_le ha
    have hex : ∃ y ∈ V.N, f y ≠ 0 := by
      by_contra hne
      push Not at hne
      let i : Fin n := ⟨0, hn⟩
      let j : Fin n := ⟨x.a, hlt⟩
      have hall : ∀ M ∈ Submodule.span Q'.ResidueField (Set.range ρ), M i j = 0 := by
        intro M hM
        induction hM using Submodule.span_induction with
        | mem _ hy =>
          obtain ⟨g, rfl⟩ := hy
          have hg : V.vr g ∈ blkMat n x.a (1 : Submodule Bh V.AA) V.N := by
            rw [← V.span]; exact Submodule.subset_span ⟨g, rfl⟩
          refine hne _ ((hg i j).2 fun hh => ?_)
          exact lt_irrefl _ (hh.1 x.a_pos)
        | zero => rfl
        | add a b _ _ ha hb => rw [Matrix.add_apply, ha, hb, add_zero]
        | smul c a _ ha => rw [Matrix.smul_apply, ha, smul_zero]
      have := hall (Matrix.single i j 1) (hs ▸ Submodule.mem_top)
      rw [Matrix.single_apply_same] at this
      exact one_ne_zero this
    obtain ⟨y, hy, hfy⟩ := hex
    obtain ⟨c, -, hc'⟩ := V.mul_mem y hy y hy
    refine ⟨y, hy, y, hy, c, fun hcQ => ?_, hc'⟩
    have := (hf c).2 hcQ
    rw [RingHom.comp_apply, ← hc', map_mul] at this
    exact hfy (mul_self_eq_zero.1 this)
  · intro hR
    refine top_of_single _ fun i j => ?_
    by_cases hij : ((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
    · refine ⟨f 1, by simp, ?_⟩
      rw [← hsing]
      exact hmem _ (single_mem_blk _ _ i j 1 (fun _ => hone) fun h' => (h' hij).elim)
    · rcases hR with ha | ⟨y, hy, z, -, b, hb, hyz⟩
      · exact (hij (by rw [ha]; exact ⟨fun _ => j.2, fun _ => i.2⟩)).elim
      · refine ⟨f y, fun h0 => hb ((hf b).1 ?_), ?_⟩
        · rw [RingHom.comp_apply, ← hyz, map_mul, h0, zero_mul]
        · rw [← hsing]
          exact hmem _ (single_mem_blk _ _ i j y (fun h' => (hij h').elim) fun _ => hy)
end
