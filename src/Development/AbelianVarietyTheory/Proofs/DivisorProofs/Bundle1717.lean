module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1680
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1683
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1655
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle003
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle004
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle219
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle179
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle180
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LeviDesc.CptLevi

open Topology

section Gen

variable {G M : Type} [Group G] [Group M] [TopologicalSpace G] [TopologicalSpace M]

theorem cptPart_map (j : M →* G) (hj : IsClosedEmbedding j) (T : Subgroup M) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  have hc : ∀ x : M, IsCompact (closure (Subgroup.zpowers (j x) : Set G)) ↔
      IsCompact (closure (Subgroup.zpowers x : Set M)) := by
    intro x
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map, hj.closure_image_eq, ← hj.isInducing.isCompact_iff]
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (hc x).1 hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hx'⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (hc x).2 hx'⟩

theorem isClosedEmbedding_unitsMap {A B : Type} [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]
    [T1Space A] [ContinuousMul A] (f : A →* B) (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (Units.map f) := by
  refine IsClosedEmbedding.of_comp (Units.isEmbedding_embedProduct (M := B)) ?_
  exact (hf.prodMap ((MulOpposite.opHomeomorph.isClosedEmbedding.comp hf).comp
    MulOpposite.opHomeomorph.symm.isClosedEmbedding)).comp Units.isClosedEmbedding_embedProduct

end Gen

section Mat

variable {R : Type} [CommRing R] {n a b : ℕ} (h : a + b = n)

def dHom : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R →* Matrix (Fin n) (Fin n) R where
  toFun p := reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h)) (fromBlocks p.1 0 0 p.2)
  map_one' := by
    simp only [Prod.fst_one, Prod.snd_one, fromBlocks_one, reindex_apply]
    exact submatrix_one_equiv _
  map_mul' p q := by
    simp only [reindex_apply, submatrix_mul_equiv, fromBlocks_multiply, Prod.fst_mul, Prod.snd_mul]
    simp

theorem dHom_apply (p : Matrix (Fin a) (Fin a) R × Matrix (Fin b) (Fin b) R) :
    dHom h p = reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks p.1 0 0 p.2) := rfl

theorem reindex_mul_reindex (e : Fin a ⊕ Fin b ≃ Fin n) (A B : Matrix (Fin a ⊕ Fin b) (Fin a ⊕ Fin b) R) :
    reindex e e A * reindex e e B = reindex e e (A * B) := by
  simp only [reindex_apply, submatrix_mul_equiv]

theorem dHom_leftInverse : Function.LeftInverse
    (fun z : Matrix (Fin n) (Fin n) R =>
      ((reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₁₁,
        (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z).toBlocks₂₂))
    (dHom h) := fun p => by
  simp only [dHom_apply, ← reindex_symm, Equiv.symm_apply_apply, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₂]

theorem isClosedEmbedding_dHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (dHom (R := R) h) := by
  refine (dHom_leftInverse h).isClosedEmbedding ?_ ?_
  · have : Continuous fun z : Matrix (Fin n) (Fin n) R =>
        reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm z :=
      continuous_id.matrix_reindex _ _
    exact (continuous_matrix fun i j => this.matrix_elem _ _).prodMk (continuous_matrix fun i j => this.matrix_elem _ _)
  · exact (continuous_fst.matrix_fromBlocks continuous_const continuous_const continuous_snd).matrix_reindex _ _

def jHom : GL (Fin a) R × GL (Fin b) R →* GL (Fin n) R :=
  (Units.map (dHom h)).comp MulEquiv.prodUnits.symm.toMonoidHom

theorem jHom_val (t : GL (Fin a) R × GL (Fin b) R) : (jHom h t).val = dHom h (t.1.val, t.2.val) := rfl

theorem isClosedEmbedding_jHom [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    IsClosedEmbedding (jHom (R := R) h) :=
  (isClosedEmbedding_unitsMap _ (isClosedEmbedding_dHom h)).comp Homeomorph.prodUnits.symm.isClosedEmbedding

theorem exists_jHom (g : GL (Fin n) R)
    (h12 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₁₂ = 0)
    (h21 : (reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val).toBlocks₂₁ = 0) :
    ∃ t, jHom h t = g := by
  set Q := reindex (finSumFinEquiv.trans (finCongr h)).symm (finSumFinEquiv.trans (finCongr h)).symm g.val with hQdef
  have hQ : Q = fromBlocks Q.toBlocks₁₁ 0 0 Q.toBlocks₂₂ := by
    have := (fromBlocks_toBlocks Q).symm
    rwa [h12, h21] at this
  have hdet : IsUnit Q.det := by
    rw [hQdef, det_reindex_self]
    exact (isUnit_iff_isUnit_det _).1 g.isUnit
  rw [hQ, det_fromBlocks_zero₁₂] at hdet
  have u1 : IsUnit Q.toBlocks₁₁ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_left hdet)
  have u2 : IsUnit Q.toBlocks₂₂ := (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hdet)
  refine ⟨(u1.unit, u2.unit), Units.ext ?_⟩
  rw [jHom_val, dHom_apply]
  simp only [IsUnit.unit_spec]
  rw [← hQ, hQdef, ← reindex_symm, Equiv.apply_symm_apply]

end Mat

variable {E : Type} [Field E] [NumberField E]

theorem blk_eq_jHom {n a b : ℕ} (h : a + b = n) (w : Pl E) (t : GLw a w × GLw b w) : blk h w t 0 = jHom h t := by
  unfold blk
  simp only [Matrix.mul_zero]
  split_ifs with hM
  · exact Units.ext (by rw [IsUnit.unit_spec]; rfl)
  · exact absurd (jHom h t).isUnit hM

theorem twCent_blk_eq {n a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (hsep : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    twCent (MonoidHom.id (GLw n w)) (blk h w m 0) = (twCent (MonoidHom.id _) m).map (jHom h) := by
  have hcop := hsep.isCoprime
  rw [blk_eq_jHom]
  ext g
  constructor
  · intro hg
    have hc : g.val * (jHom h m).val = (jHom h m).val * g.val := by
      have := congrArg Units.val (show g * jHom h m = jHom h m * MonoidHom.id _ g from hg)
      simpa using this
    set e := finSumFinEquiv.trans (finCongr h) with he
    set Q := reindex e.symm e.symm g.val with hQdef
    have hgQ : g.val = reindex e e Q := by simp [hQdef]
    rw [hgQ, jHom_val, dHom_apply, ← fromBlocks_toBlocks Q, reindex_mul_reindex, reindex_mul_reindex] at hc
    have hc2 := (reindex e e).injective hc
    simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hc2
    rw [Matrix.fromBlocks_inj] at hc2
    have h21 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop hc2.2.2.1
    have h12 := GlobalTheory.LeviDesc.intertwiner_eq_zero_of_isCoprime _ _ _ hcop.symm hc2.2.1
    obtain ⟨t, rfl⟩ := exists_jHom h g h12 h21
    refine ⟨t, ?_, rfl⟩
    show t * m = m * MonoidHom.id _ t
    apply (isClosedEmbedding_jHom h).injective
    have : jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t) := hg
    simpa [map_mul] using this
  · rintro ⟨t, ht, rfl⟩
    have : t * m = m * t := ht
    show jHom h t * jHom h m = jHom h m * MonoidHom.id _ (jHom h t)
    rw [MonoidHom.id_apply, ← map_mul, ← map_mul, this]

theorem isClosed_parP' (a n : ℕ) (w : Pl E) : IsClosed (GlobalTheory.LeviDesc.parP a n w : Set (GLw n w)) := by
  have : (parP a n w : Set (GLw n w)) = ⋂ i : Fin n, ⋂ j : Fin n,
      {g : GLw n w | decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ)) → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j = 0} := by
    ext g
    simp only [Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases hij : decide (a ≤ (j : ℕ)) < decide (a ≤ (i : ℕ))
  · simp only [hij, true_implies]
    exact isClosed_eq (Continuous.matrix_elem (Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion E))) i j) continuous_const
  · simp only [hij, false_implies, Set.ofPred_true]
    exact isClosed_univ

theorem mem_compactPart_parabolic_iff : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w), (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ (hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w) (p : GlobalTheory.LeviDesc.parP a n w), p ∈ cptPart (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w)) ↔ ∃ t ∈ cptPart (twCent (MonoidHom.id _) m), blk h w t 0 = (p : GLw n w) := by
  intro E _ _ n a b h w m hsep hγ p
  have hT := GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hsep
  rw [← Subgroup.mem_map_iff_mem (f := (parP a n w).subtype) (parP a n w).subtype_injective,
    GlobalTheory.IwRed.cptPart_map_sub _ (isClosed_parP' a n w) _ hγ hT, twCent_blk_eq h w m hsep,
    cptPart_map _ (isClosedEmbedding_jHom h)]
  simp only [Subgroup.mem_map, blk_eq_jHom, Subgroup.coe_subtype]

end GlobalTheory.LeviDesc.CptLevi
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.eventually_isIntegral_of_integralCoordsLocalTensor : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), ∀ᶠ w : AwayP p in Filter.cofinite,
    ∀ x : w.1.adicCompletion ℚ ⊗[ℚ] G.C, IntC G w x → (∃ f : Polynomial (w.1.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ w.1.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) := by
  first | (exact @GlobalTheory.FinClsLoc.intC_isIntegral) | (exact GlobalTheory.FinClsLoc.intC_isIntegral) | (intros; apply GlobalTheory.FinClsLoc.intC_isIntegral  <;> assumption)
end

section

set_option autoImplicit false

namespace GlobalTheory.PrimePart

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes

section ResidueField

variable {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {d : ℕ}

theorem sqrtNeg_ne_neg (h2 : p ≠ 2) (hd : (d : ZMod p) ≠ 0) {r : k} (hr : r ^ 2 = -(d : k)) : r ≠ -r := by
  intro h
  have h2k : (2 : k) ≠ 0 := by
    intro h0
    have : p ∣ 2 := (CharP.cast_eq_zero_iff k p 2).1 (by exact_mod_cast h0)
    exact h2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hr0 : r = 0 := by
    have : 2 * r = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left h2k
  have hdk : (d : k) = 0 := by
    rw [hr0] at hr
    linear_combination hr
  exact hd ((ZMod.natCast_eq_zero_iff d p).2 ((CharP.cast_eq_zero_iff k p d).1 hdk))

theorem sqrtNeg_pow_of_isSquare (hs : IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) : r ^ p = r := by
  obtain ⟨m, hm⟩ := hs
  have h1 : r ^ 2 = (ZMod.castHom (dvd_refl p) k m) ^ 2 := by
    rw [hr, ← map_pow, sq, ← hm, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · rw [h, ← map_pow, ZMod.pow_card]
  · rw [h, ← map_neg, ← map_pow, ZMod.pow_card]

theorem sqrtNeg_pow_ne_of_not_isSquare (hs : ¬ IsSquare (-(d : ZMod p))) {r : k} (hr : r ^ 2 = -(d : k)) :
    r ^ p ≠ r := by
  have hd : (d : ZMod p) ≠ 0 := fun h => hs (by rw [h, neg_zero]; exact IsSquare.zero)
  have hd' : -(d : ZMod p) ≠ 0 := neg_ne_zero.2 hd
  have h2 : p ≠ 2 := by
    rintro rfl
    apply hs
    generalize (-(d : ZMod 2)) = x
    exact ⟨x, by rw [← sq, ZMod.pow_card]⟩
  have he : (-(d : ZMod p)) ^ (p / 2) = -1 :=
    (ZMod.pow_div_two_eq_neg_one_or_one p hd').resolve_left fun h => hs ((ZMod.euler_criterion p hd').2 h)
  have hk : (-(d : k)) ^ (p / 2) = -1 := by
    have := congrArg (ZMod.castHom (dvd_refl p) k) he
    rwa [map_pow, map_neg, map_neg, map_natCast, map_one] at this
  have hp : p = 2 * (p / 2) + 1 := by
    have := (Fact.out : p.Prime).eq_two_or_odd.resolve_left h2
    omega
  have h3 : r ^ p = -r := by
    conv_lhs => rw [hp]
    rw [pow_succ, pow_mul, hr, hk, neg_one_mul]
  rw [h3]
  exact (sqrtNeg_ne_neg h2 hd hr).symm

end ResidueField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}

theorem label_rt_sq (H : Host E) (σ : E →+* ℂ) : σ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  have := congrArg (σ.comp (algebraMap (𝓞 E) E)) H.rt_sq
  rwa [map_pow, map_neg, map_natCast] at this

theorem conj_label_rt (H : Host E) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ (H.rt : E) = -σ (H.rt : E) := by
  rw [ComplexEmbedding.conjugate_coe_eq]
  have h := label_rt_sq H σ
  generalize σ (H.rt : E) = z at h
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [sq] at h1 h2
  have h3 : z.re = 0 := by
    by_contra h0
    have h4 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [h4] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [h3]

theorem exists_w0_sq_even_constant (H : Host E) : ∃ n : ℕ, H.w0 ^ 2 = H.w0 - 2 * n := by
  refine ⟨(H.d + 1) / 8, ?_⟩
  have h8 : ((H.d : ℕ) : 𝓞 E) + 1 = 8 * (((H.d + 1) / 8 : ℕ) : 𝓞 E) := by
    have : H.d + 1 = 8 * ((H.d + 1) / 8) := by have := H.d_mod; omega
    exact_mod_cast this
  have h4 : (4 : 𝓞 E) ≠ 0 := by norm_num
  apply mul_left_cancel₀ h4
  have h1 := H.two_weight_eq_one_add_root
  have h2 := H.rt_sq
  linear_combination (2 * H.w0 - 1 + H.rt) * h1 + h2 - h8

variable {c : Coeff l} {T : CDVR} (io : c.F →+* T.Fr) {p : ℕ} [Fact p.Prime] (X : ValExt T p)

theorem red_eq_of_label_eq {σ σ' : E →+* ℂ} {a b : 𝓞 E} (h : σ' (a : E) = σ (b : E)) :
    red io X σ' a = red io X σ b := by
  have h1 : embK c σ' a = embK c σ b := Subtype.ext h
  have h2 : embO io X σ' a = embO io X σ b := X.ints.hom_inj (by
    rw [algebraMap_embO, algebraMap_embO, embX, embX, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
      RingHom.comp_apply, h1])
  rw [red, red, RingHom.comp_apply, RingHom.comp_apply, h2]

theorem frobOnType : FrobOnType io X := by
  intro σ σ' hF
  haveI := charP_residueField_of_irreducible X
  have hred : ∀ a, red io X σ' a = red io X σ a ^ p := fun a => (red_eq_pow_iff io X σ σ' a p).2 (hF a)
  have hr : red io X σ H.rt ^ 2 = -(H.d : ResidueField X.O) := by
    rw [← map_pow, H.rt_sq, map_neg, map_natCast]
  have hpm : σ' (H.rt : E) = σ (H.rt : E) ∨ σ' (H.rt : E) = -σ (H.rt : E) :=
    sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [label_rt_sq, label_rt_sq])
  refine ⟨fun hs => ?_, fun hi => ?_⟩
  · have key : σ' (H.rt : E) = σ (H.rt : E) := by
      refine hpm.resolve_right fun h => ?_
      by_cases h2 : p = 2
      · subst h2
        obtain ⟨n, hn⟩ := exists_w0_sq_even_constant H
        have hw : ∀ τ : E →+* ℂ, 2 * τ (H.w0 : E) = 1 + τ (H.rt : E) := fun τ => by
          have := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        have h1 : σ' (H.w0 : E) = σ ((1 - H.w0 : 𝓞 E) : E) := by
          have e : σ ((1 - H.w0 : 𝓞 E) : E) = 1 - σ (H.w0 : E) := by
            have := map_sub (σ.comp (algebraMap (𝓞 E) E)) 1 H.w0
            rwa [map_one] at this
          rw [e]
          linear_combination (1 / 2) * hw σ' + (1 / 2) * hw σ + (1 / 2) * h
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, ← map_pow, hn, map_sub, map_sub, map_mul, map_one, map_ofNat] at h3
        have h4 : (2 : ResidueField X.O) = 0 := by
          exact_mod_cast CharP.cast_eq_zero (ResidueField X.O) 2
        apply one_ne_zero (α := ResidueField X.O)
        linear_combination -h3 + (red io X σ H.w0 - red io X σ n) * h4
      · have h1 : σ' (H.rt : E) = σ ((-H.rt : 𝓞 E) : E) := by
          rw [h]; exact (map_neg (σ.comp (algebraMap (𝓞 E) E)) H.rt).symm
        have h3 := red_eq_of_label_eq io X h1
        rw [hred, sqrtNeg_pow_of_isSquare hs.2 hr, map_neg] at h3
        exact sqrtNeg_ne_neg h2 hs.1 hr h3
    rw [InPsi, InPsi, key]
  · have key : σ' (H.rt : E) = -σ (H.rt : E) := by
      refine hpm.resolve_left fun h => ?_
      have h3 := red_eq_of_label_eq io X h
      rw [hred] at h3
      exact sqrtNeg_pow_ne_of_not_isSquare hi hr h3
    rw [InPsi, InPsi, key, conj_label_rt]

theorem frobOnType_all (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l)
    (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) : FrobOnType io X :=
  frobOnType io X

end GlobalTheory.PrimePart
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartAct

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart GlobalTheory.LawLog

theorem logOf_eq {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} (G : Germ.FGLaw k d) (i : Fin d) :
    GlobalTheory.FormalLog.logOf G i = ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i := rfl

theorem subst_act_log {k O : Type} [CommRing k] [Algebra ℚ k] [CommRing O] {d : ℕ} (G : Germ.FGLaw k d)
    (A : Germ.OAct O G) (a : O) (b : Fin d) :
    subst (fun i => subst (oneVar k d) (A.act a i)) (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G b)) =
      ∑ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a b) •
        (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G j) : MvPowerSeries (Fin d) k) := by

  rw [subst_oneVar _ cc_oneVar _ (A.const a), logOf_eq, GlobalTheory.TwistCheck.log_act, ← coe_substAlgHom hs_oneVar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem isIntHom_actX_and_eigen (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (a : 𝓞 E) :
    IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧
      ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  refine ⟨⟨fun b => ?_, fun b α => ?_, fun b => ?_⟩, fun ℓ => ?_⟩
  · refine constantCoeff_subst_eq_zero hs_oneVar cc_oneVar ?_
    rw [constantCoeff_map, (GlobalTheory.IntChartCheck.const_zero Ch).2 a b, map_zero]
  · have e : actX Ch X a b = map (jX X) (subst (oneVar T.V _) (Ch.actT a b)) := by
      rw [actX, map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact isIntV_jX X _
  · let _ := io.toAlgebra
    let A : Germ.OAct (𝓞 E) (lawX Ch X) := GlobalTheory.FBMap.mapAct X.ιF Ch.ch.B.A
    have hA : ∀ i, A.act a i = map (jX X) (Ch.actT a i) := fun i => by
      show map X.ιF (Ch.ch.B.A.act a i) = _
      rw [Ch.gen.1.2.1 a i, jX, map_comp]; rfl
    have h := subst_act_log (lawX Ch X) A a b
    simp only [hA, coeff_map] at h
    exact h
  · obtain ⟨χ, hχ⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir.exists_char c T io ℓ.1
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a (χ a) (hχ a)
    have hz : embX io X ℓ.1 a = jX X (χ a) := by
      rw [jX, RingHom.comp_apply, hχ]; rfl
    funext i
    have h2 := congrArg (jX X) (congrFun h i)

    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply, smul_eq_mul] at h2
    rw [hz]
    simpa only [Matrix.mulVec, dotProduct, tanX, lieVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] using h2

end GlobalTheory.ChartAct
end
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem exists_realPart_hom : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (A : Frames V), V.SigOK → IsInfFam θ → IsFrames V A → ∃ rp : GA D V →* (∀ ρ, Upq V ρ), Continuous rp ∧ IsRealPart V θ A rp := by
  intro D V θ A hV hθ hA
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau
  obtain ⟨hcm, -⟩ := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  obtain ⟨e1, he1⟩ := GlobalTheory.Mem.InfGroup.real_points D.host.F D.host.E D.sp.cm.sig V.rank V.gram D.what₂.Tau (tauE D) θ
    (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) A hcm hτ hθ (fun i => hV (tauE D i)) hA
  obtain ⟨e0, he0⟩ := GlobalTheory.Mem.VolSplit.exists_adelic_split D.host.F D.host.E D.sp.cm.sig V.rank V.gram
  refine ⟨e1.toMulEquiv.toMonoidHom.comp ((MonoidHom.fst _ _).comp e0.toMulEquiv.toMonoidHom),
    e1.continuous.comp (continuous_fst.comp e0.continuous), fun h i => ?_⟩
  show UpqT.mat (e1 (e0 h).1 i) * A i = _
  rw [he1, (he0 h).2]; rfl

end GlobalTheory.CovTop.VolUp
end
