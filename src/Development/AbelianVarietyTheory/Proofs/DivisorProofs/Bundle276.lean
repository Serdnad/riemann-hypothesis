module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle072
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle076
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle087
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle166
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle169
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle186
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc


theorem _root_.GlobalTheory.T.card_blockParabolicSubgroupGL : ∀ (R : Type) [CommRing R] [Finite R] (a d : ℕ), a ≤ d →
    Nat.card (blockPar R a d) = Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by
  first | exact @GlobalTheory.StdLoc.card_blockPar | exact GlobalTheory.StdLoc.card_blockPar | (intros; apply GlobalTheory.StdLoc.card_blockPar <;> assumption)
end

section

open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc


theorem _root_.GlobalTheory.T.card_GL_ringOfIntegers_quotient_prod_factors : ∀ (E : Type) [Field E] [NumberField E] (𝔪 : Ideal (𝓞 E)), 𝔪 ≠ ⊥ → ∀ n : ℕ,
    (Nat.card (GL (Fin n) (𝓞 E ⧸ 𝔪)) : ℝ) = ∏ w ∈ (normalizedFactors 𝔪).toFinset,
      (Ideal.absNorm w : ℝ) ^ ((normalizedFactors 𝔪).count w * n ^ 2) * glVol (Ideal.absNorm w : ℝ) n := by
  first | exact @GlobalTheory.CardGLQuot.card_GL_quot_prod | exact GlobalTheory.CardGLQuot.card_GL_quot_prod | (intros; apply GlobalTheory.CardGLQuot.card_GL_quot_prod <;> assumption)
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap (RingHom.id B) (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  first | exact @GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | exact GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | (intros; apply GlobalTheory.KummerAlg.finite_projective_faithfullyFlat <;> assumption)
end

section

open scoped Classical

theorem _root_.GlobalTheory.T.finsum_stabilizer_weighted_pair_orbits_conjClass : ∀ (G : Type) [Group G] (X : Type) [MulAction G X] (Γ : Subgroup G) (Φ : Γ → X → ℂ),
    (∀ δ γ : Γ, ∀ x : X, Φ (δ * γ * δ⁻¹) ((δ : G) • x) = Φ γ x) →
    ∀ γ₀ : Γ, ∑ᶠ O : {O : MulAction.orbitRel.Quotient Γ (GlobalTheory.MassConj.ConjPair Γ X) //
        ConjClasses.mk (Quotient.out O).elt = ConjClasses.mk γ₀},
        (1 / (Nat.card (MulAction.stabilizer Γ (Quotient.out O.1)) : ℂ)) *
          Φ (Quotient.out O.1).elt (Quotient.out O.1).pt =
      ∑ᶠ b : MulAction.orbitRel.Quotient (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G) X,
        (1 / (Nat.card (MulAction.stabilizer (Γ ⊓ Subgroup.centralizer {(γ₀ : G)} : Subgroup G)
          (Quotient.out b)) : ℂ)) * Φ γ₀ (Quotient.out b) := by
  first | (exact @GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (exact GlobalTheory.MassConj.finsum_pairOrbit_fibre) | (intros; apply GlobalTheory.MassConj.finsum_pairOrbit_fibre  <;> assumption)
end

section

open scoped Classical

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

def ConjTgt (H : Type) [Group H] (_K : Subgroup H) : Type := H

variable {H X : Type} [Group H] [MulAction H X]

def ConjTgt.val {K : Subgroup H} (γ : ConjTgt H K) : H := γ

instance (K : Subgroup H) : MulAction K (ConjTgt H K) where
  smul k γ := ((k : H) * (show H from γ) * (k : H)⁻¹ : H)
  one_smul := by
    show ∀ γ : H, (1 : H) * γ * (1 : H)⁻¹ = γ
    intro γ; group
  mul_smul k l := by
    show ∀ γ : H, ((k : H) * l) * γ * ((k : H) * l)⁻¹ = (k : H) * ((l : H) * γ * (l : H)⁻¹) * (k : H)⁻¹
    intro γ; group

theorem mk_smul' {T α : Type} [Group T] [MulAction T α] (t : T) (x : α) :
    (Quotient.mk'' (t • x) : orbitRel.Quotient T α) = Quotient.mk'' x :=
  Quotient.sound' (mem_orbit x t)

theorem exists_smul_eq_out' {T α : Type} [Group T] [MulAction T α] (q : orbitRel.Quotient T α) (x : α)
    (h : (Quotient.mk'' x : orbitRel.Quotient T α) = q) : ∃ t : T, t • x = Quotient.out q := by
  have h2 : (Quotient.mk'' (Quotient.out q) : orbitRel.Quotient T α) = Quotient.mk'' x := by
    rw [h]; exact Quotient.out_eq' q
  exact orbitRel_apply.1 (Quotient.eq''.1 h2)

end GlobalTheory.PtFib

namespace GlobalTheory.PtFib

open MulAction GlobalTheory.MassConj

variable {H X : Type} [Group H] [MulAction H X]

theorem card_stab_pair (x : X) (γ : H) :
    Nat.card (stabilizer (stabilizer H x) (show ConjTgt H (stabilizer H x) from γ)) =
      Nat.card (stabilizer H (ConjPair.mk γ x : ConjPair H X)) := by
  apply Nat.card_congr
  refine
   { toFun := fun k => ⟨((k : stabilizer H x) : H), ?_⟩
     invFun := fun d => ⟨⟨(d : H), ?_⟩, ?_⟩
     left_inv := fun k => rfl
     right_inv := fun d => rfl }
  · have hk : ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ = γ := k.2
    rw [GlobalTheory.MassConj.mem_stabilizer_iff]
    refine ⟨?_, (k : stabilizer H x).2⟩
    calc ((k : stabilizer H x) : H) * γ
        = ((k : stabilizer H x) : H) * γ * ((k : stabilizer H x) : H)⁻¹ * ((k : stabilizer H x) : H) := by group
      _ = γ * ((k : stabilizer H x) : H) := by rw [hk]
  · exact ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).2
  · have hd := ((GlobalTheory.MassConj.mem_stabilizer_iff _ _).1 d.2).1
    rw [MulAction.mem_stabilizer_iff]
    show (d : H) * γ * (d : H)⁻¹ = γ
    rw [hd]; group

theorem card_stab_smul (t : H) (p : ConjPair H X) :
    Nat.card (stabilizer H (t • p)) = Nat.card (stabilizer H p) :=
  (Nat.card_congr (stabilizerEquivStabilizer (rfl : t • p = t • p)).toEquiv).symm

theorem mk_out_pt (p : ConjPair H X) :
    (Quotient.mk'' (Quotient.out (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X))).pt :
      orbitRel.Quotient H X) = Quotient.mk'' p.pt := by
  obtain ⟨t, ht⟩ := exists_smul_eq_out' (Quotient.mk'' p : orbitRel.Quotient H (ConjPair H X)) p rfl
  rw [← ht, smul_pt, mk_smul']

theorem ptFib_mass (H : Type) [Group H] (X : Type) [MulAction H X] (f : H → X → ℂ)
    (hf : ∀ δ γ : H, ∀ x : X, f (δ * γ * δ⁻¹) (δ • x) = f γ x)
    (hfin : ∀ x : X, Finite (MulAction.stabilizer H x))
    (hsupp : ∀ x : X, (Function.support fun γ : H => f γ x).Finite) (x : X) :
    ∑ᶠ O : {O : MulAction.orbitRel.Quotient H (GlobalTheory.MassConj.ConjPair H X) //
        (Quotient.mk'' (Quotient.out O).pt : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x},
        (1 / (Nat.card (MulAction.stabilizer H (Quotient.out O.1)) : ℂ)) *
          f (Quotient.out O.1).elt (Quotient.out O.1).pt =
      (1 / (Nat.card (MulAction.stabilizer H x) : ℂ)) * ∑ᶠ γ : H, f γ x := by
  haveI := hfin x
  let K := stabilizer H x
  let F : ConjTgt H K → ℂ := fun γ => f γ x
  have hF : ∀ (k : K) (γ : ConjTgt H K), F (k • γ) = F γ := by
    intro k γ
    change H at γ
    show f ((k : H) * γ * (k : H)⁻¹) x = f γ x
    have h := hf k γ x
    rwa [show (k : H) • x = x from k.2] at h
  have key := GlobalTheory.finsum_orbits_stabilizer_mass F hF (hsupp x)
  let g : ConjTgt H K → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    fun γ => ⟨Quotient.mk'' (ConjPair.mk (H := H) γ x), by rw [mk_out_pt]⟩
  have hg : ∀ a b : ConjTgt H K, a ∈ orbit K b → g a = g b := by
    rintro a b ⟨k, hk⟩
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) = Quotient.mk'' (ConjPair.mk (H := H) b x)
    have : (ConjPair.mk (H := H) a x : ConjPair H X) = (k : H) • ConjPair.mk (H := H) b x := by
      ext
      · rw [smul_elt, ← hk]; rfl
      · rw [smul_pt]; exact k.2.symm
    rw [this, mk_smul']
  let φ : orbitRel.Quotient K (ConjTgt H K) → {O : orbitRel.Quotient H (ConjPair H X) //
      (Quotient.mk'' (Quotient.out O).pt : orbitRel.Quotient H X) = Quotient.mk'' x} :=
    Quotient.lift g (fun a b hab => hg a b (orbitRel_apply.1 hab))
  have hφ : ∀ γ : ConjTgt H K, φ (Quotient.mk'' γ) = g γ := fun γ => rfl
  have hinj : Function.Injective φ := by
    intro o1 o2 h
    induction o1 using Quotient.inductionOn' with | h a => ?_
    induction o2 using Quotient.inductionOn' with | h b => ?_
    rw [hφ, hφ] at h
    have h1 : (Quotient.mk'' (ConjPair.mk (H := H) a x) : orbitRel.Quotient H (ConjPair H X)) =
        Quotient.mk'' (ConjPair.mk (H := H) b x) := congrArg Subtype.val h
    obtain ⟨δ, hδ⟩ := orbitRel_apply.1 (Quotient.eq''.1 h1)
    have he : δ * ConjTgt.val b * δ⁻¹ = ConjTgt.val a := congrArg ConjPair.elt hδ
    have hp : δ • x = x := congrArg ConjPair.pt hδ
    apply Quotient.sound'
    exact orbitRel_apply.2 ⟨⟨δ, hp⟩, he⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨O, hO⟩
    obtain ⟨t, ht⟩ := orbitRel_apply.1 (Quotient.eq''.1 hO)

    refine ⟨Quotient.mk'' (show ConjTgt H K from (t⁻¹ * (Quotient.out O).elt * t : H)), ?_⟩
    rw [hφ]
    apply Subtype.ext
    show (Quotient.mk'' (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x) :
      orbitRel.Quotient H (ConjPair H X)) = O
    have : (ConjPair.mk (t⁻¹ * (Quotient.out O).elt * t) x : ConjPair H X) = t⁻¹ • Quotient.out O := by
      ext
      · rw [smul_elt]; group
      · rw [smul_pt, ← ht, inv_smul_smul]
    rw [this, mk_smul']
    exact Quotient.out_eq' O
  let e := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  rw [← finsum_comp_equiv e]
  have hterm : ∀ o : orbitRel.Quotient K (ConjTgt H K),
      (1 / (Nat.card (stabilizer H (Quotient.out (e o).1)) : ℂ)) *
          f (Quotient.out (e o).1).elt (Quotient.out (e o).1).pt =
        ((Nat.card (stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * F (Quotient.out o) := by
    intro o
    have h1 : (e o).1 = Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) := by
      show (φ o).1 = _
      conv_lhs => rw [← Quotient.out_eq' o]
      rfl
    rw [h1]
    obtain ⟨t, ht⟩ := exists_smul_eq_out'
      (Quotient.mk'' (ConjPair.mk (H := H) (Quotient.out o) x) : orbitRel.Quotient H (ConjPair H X)) _ rfl
    rw [← ht, card_stab_smul, smul_elt, smul_pt, hf, ← card_stab_pair, one_div]
    rfl
  rw [finsum_congr hterm, key, one_div]
  rfl

end GlobalTheory.PtFib
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.isSelfDual_image_standardLattice_unitary : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) K), (g.map σ)ᵀ * g = 1 →
    SelfDual O σ (matLat O g (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.selfDual_matLat_stdLat | exact GlobalTheory.LatOrb.selfDual_matLat_stdLat | (intros; apply GlobalTheory.LatOrb.selfDual_matLat_stdLat <;> assumption)
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  first | exact @GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | exact GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | (intros; apply GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual <;> assumption)
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.isFullRankLattice_image_standardLattice_GL : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (g : GL (Fin n) K),
    IsLatV O (matLat O g.val (stdLat O n)) := by
  first | exact @GlobalTheory.LatOrb.matLat_stdLat_isLatV | exact GlobalTheory.LatOrb.matLat_stdLat_isLatV | (intros; apply GlobalTheory.LatOrb.matLat_stdLat_isLatV <;> assumption)
end

section

open Polynomial Matrix GlobalTheory.LatOrb

theorem _root_.GlobalTheory.T.isIntegral_matrix_of_mapsTo_fullRankLattice : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (n : ℕ) (M : Submodule O (Fin n → K)),
    IsLatV O M → ∀ c : Matrix (Fin n) (Fin n) K, (∀ v ∈ M, c *ᵥ v ∈ M) → IsIntegral O c := by
  first | exact @GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | exact GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice | (intros; apply GlobalTheory.LatOrb.isIntegral_of_mapsTo_lattice <;> assumption)
end

section

open scoped TensorProduct

noncomputable section
namespace GlobalTheory.WtRank

abbrev chr (k : Type) [Field k] (C : Type) [CommRing C] (χ : C →+* k) : k ⊗[ℤ] C →ₐ[k] k :=
  Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem finrank_fix {k A M : Type*} [Field k] [CommRing A] [Algebra k A] [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] [FiniteDimensional k M] (e : A) (W : Submodule k M)
    (hW : ∀ m, m ∈ W ↔ e • m = m) :
    Module.finrank k W = Module.finrank k (M ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A M)) := by
  set f : M →ₗ[k] M := DistribSMul.toLinearMap k M (1 - e)
  have hker : W = LinearMap.ker f := by
    ext m
    rw [hW, LinearMap.mem_ker]
    simp only [f, DistribSMul.toLinearMap_apply, sub_smul, one_smul, sub_eq_zero, eq_comm]
  have hrange : (Ideal.span {1 - e} • ⊤ : Submodule A M).restrictScalars k = LinearMap.range f := by
    ext m
    rw [Submodule.restrictScalars_mem, Submodule.ideal_span_singleton_smul, LinearMap.mem_range,
      Submodule.mem_smul_pointwise_iff_exists]
    simp [f]
  have e1 := (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {1 - e} • ⊤ : Submodule A M)).finrank_eq
  rw [← e1, hrange, hker]
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  omega

theorem weight_finrank_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (C : Type) [CommRing C] [Module.Free ℤ C] [Module.Finite ℤ C] (H : Type 1) [AddCommGroup H] [Module k H] [FiniteDimensional k H] (σ : C →+* Module.End k H), (letI : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom; Module.Projective (k ⊗[ℤ] C) H) → ∀ χ : C →+* k, Module.finrank k ↥(⨅ c : C, (σ c).maxGenEigenspace (χ c)) = Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) * Module.finrank k ↥(⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) := by
  intro k _ _ C _ _ _ H _ _ _ σ
  letI inst : Module (k ⊗[ℤ] C) H := Module.compHom H (Algebra.TensorProduct.lift
    (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)).toRingHom
  intro hP χ
  have hP' : Module.Projective (k ⊗[ℤ] C) H := hP
  have hact : ∀ (a : k ⊗[ℤ] C) (h : H), a • h = (Algebra.TensorProduct.lift
      (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom (fun _ _ => Algebra.commutes _ _)) a h := fun _ _ => rfl
  haveI : IsScalarTower k (k ⊗[ℤ] C) H := ⟨fun l a h => by
    rw [hact, hact, map_smul, LinearMap.smul_apply]⟩
  obtain ⟨e, he, h1, hn⟩ := GlobalTheory.T.exists_idempotent_local_of_character k (k ⊗[ℤ] C) (chr k C χ)
  have hσ : ∀ c, σ c = DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext h
    rw [DistribSMul.toLinearMap_apply, hact]
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hlm : ∀ c, ((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c =
      DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c) := by
    intro c; ext x
    simp [Algebra.TensorProduct.includeRight_apply]
  have eH : (⨅ c : C, (σ c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k H ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hσ]
  have eA : (⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (χ c)) =
      ⨅ c : C, Module.End.maxGenEigenspace (DistribSMul.toLinearMap k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c)) (χ c) :=
    iInf_congr fun c => by rw [hlm]
  rw [eH, eA]
  rw [finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C H χ e he h1 hn), finrank_fix e _ (GlobalTheory.T.mem_iInf_maxGenEigenspace_iff_smul_eq k C (k ⊗[ℤ] C) χ e he h1 hn),
    GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul k (k ⊗[ℤ] C) (chr k C χ) e he h1 hn H]
  have hq : Module.finrank k (H ⧸ GlobalTheory.HTRho.mSub σ χ ⊤) =
      Module.finrank k (H ⧸ (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H)) := by
    have heq : GlobalTheory.HTRho.mSub σ χ ⊤ = (RingHom.ker (chr k C χ) • ⊤ : Submodule (k ⊗[ℤ] C) H).restrictScalars k := by
      ext x; rw [Submodule.restrictScalars_mem]; exact GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul k C H σ χ x
    rw [heq]; exact (Submodule.Quotient.restrictScalarsEquiv k _).finrank_eq
  rw [hq]
  congr 1
  have hI : (Ideal.span {1 - e} • ⊤ : Submodule (k ⊗[ℤ] C) (k ⊗[ℤ] C)) = Ideal.span {1 - e} := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  exact ((Submodule.quotEquivOfEq _ _ hI).restrictScalars k).finrank_eq.symm

end GlobalTheory.WtRank
end
end

section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.sq_mul_finrank_matrixAlgebra_hom_eq_finrank_mul : ∀ (k : Type) [Field k] (m : ℕ) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (ρX : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k X) (ρY : Matrix (Fin m) (Fin m) k →ₐ[k] Module.End k Y), m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom) = Module.finrank k X * Module.finrank k Y := by
  first | (exact @GlobalTheory.MatCount.count) | (exact GlobalTheory.MatCount.count) | (intros; apply GlobalTheory.MatCount.count <;> assumption)
end

section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitaryStandardLatticeAlternatingForm_bijective : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  first | exact @GlobalTheory.UnitaryStd.form_bijective_of_unimodular | exact GlobalTheory.UnitaryStd.form_bijective_of_unimodular | (intros; apply GlobalTheory.UnitaryStd.form_bijective_of_unimodular <;> assumption)
end
