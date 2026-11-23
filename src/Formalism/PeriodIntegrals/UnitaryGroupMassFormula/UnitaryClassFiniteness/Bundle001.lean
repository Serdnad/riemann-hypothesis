module

public import Formalism.PeriodIntegrals.Bundle004
public import Formalism.PeriodIntegrals.Bundle009
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open Matrix NumberField
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.HermLatFin

variable {E : Type} [Field E] {M : ℕ} (σ : E →+* E) (J : Matrix (Fin M) (Fin M) E)

theorem herm_add_left (x x' y : Fin M → E) : herm σ J (x + x') y = herm σ J x y + herm σ J x' y := by
  simp only [herm, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem herm_add_right (x y y' : Fin M → E) : herm σ J x (y + y') = herm σ J x y + herm σ J x y' := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem herm_smul_left (a : E) (x y : Fin M → E) : herm σ J (a • x) y = σ a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_smul_right (a : E) (x y : Fin M → E) : herm σ J x (a • y) = a * herm σ J x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_zero_left (y : Fin M → E) : herm σ J 0 y = 0 := by
  simp [herm]

theorem herm_zero_right (x : Fin M → E) : herm σ J x 0 = 0 := by
  simp [herm]

theorem herm_scale (D : E) (x y : Fin M → E) : herm σ (D • J) x y = D * herm σ J x y := by
  simp only [herm, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem herm_single_left (i : Fin M) (k : ℕ) (y : Fin M → E) :
    herm σ J (Pi.single i (k : E)) y = (k : E) * (J.mulVec y) i := by
  classical
  simp only [herm]
  rw [Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · simp

variable [NumberField E]

theorem fg_of_den (N : Submodule (𝓞 E) (Fin M → E)) (d : ℕ) (hd : 0 < d)
    (h : ∀ y ∈ N, ∀ j, IsIntegral ℤ ((d : E) * y j)) : N.FG := by
  classical

  let f : (Fin M → 𝓞 E) →ₗ[𝓞 E] (Fin M → E) :=
    LinearMap.pi fun j => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj j)
  let sc : (Fin M → E) →ₗ[𝓞 E] (Fin M → E) := (d : 𝓞 E) • LinearMap.id
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have hsc : ∀ y : Fin M → E, ∀ j, sc y j = (d : E) * y j := by
    intro y j
    simp [sc, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  have hinj : Function.Injective sc := by
    intro x y hxy
    funext j
    have := congrFun hxy j
    rw [hsc, hsc] at this
    exact mul_left_cancel₀ hd' this
  have hle : N.map sc ≤ LinearMap.range f := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun j => ⟨(d : E) * y j, h y hy j⟩, ?_⟩
    funext j
    rw [hsc]
    rfl
  have hfg : (N.map sc).FG := by
    rw [← Submodule.map_comap_eq_of_le hle]
    exact (IsNoetherian.noetherian _).map f
  exact Submodule.fg_of_fg_map_injective sc hinj hfg

theorem sub_finite (N : Submodule (𝓞 E) (Fin M → E)) (hN : N.FG) (n : ℕ) (hn : 0 < n) :
    {s : Set (Fin M → E) | (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
      (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N}.Finite := by
  classical
  haveI : Module.Finite (𝓞 E) N := Module.Finite.iff_fg.2 hN
  haveI : Module.Finite ℤ N := Module.Finite.trans (𝓞 E) N
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := N)

  let rep : (S → Fin n) → (Fin M → E) := fun c => ∑ g : S, ((c g : ℕ) : ℤ) • ((g : N) : Fin M → E)
  let T : Set (Fin M → E) := Set.range rep
  have hT : T.Finite := Set.finite_range rep
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hdec : ∀ x ∈ N, ∃ t ∈ T, ∃ z ∈ N, x = t + (n : E) • z := by
    intro x hx
    have hmem : (⟨x, hx⟩ : N) ∈ Submodule.span ℤ (S : Set N) := by rw [hS]; trivial
    obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hmem
    have hx' : x = ∑ g ∈ S, a g • ((g : N) : Fin M → E) := by
      have := congrArg Subtype.val ha
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    let c : S → Fin n := fun g => ⟨(a g % n).toNat, by
      have h1 := Int.emod_nonneg (a g) hnZ.ne'
      have h2 := Int.emod_lt_of_pos (a g) hnZ
      omega⟩
    refine ⟨rep c, ⟨c, rfl⟩, ∑ g ∈ S, (a g / n) • ((g : N) : Fin M → E), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ g.2
    · have hc : ∀ g : S, (((c g : ℕ) : ℤ)) = a g % n := fun g => by
        simp only [c]
        exact Int.toNat_of_nonneg (Int.emod_nonneg _ hnZ.ne')
      simp only [rep, hc]
      rw [Finset.sum_coe_sort S (fun g => (a g % (n : ℤ)) • ((g : N) : Fin M → E)), hx',
        Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Int.cast_smul_eq_zsmul E, smul_comm ((n : E)) _ _, ← Int.cast_smul_eq_zsmul E (a g / n),
        smul_smul, ← Int.cast_smul_eq_zsmul E (a g % n), ← add_smul]
      congr 1
      have h2 : ((a g : ℤ) : E) = ((a g % n : ℤ) : E) + (n : E) * ((a g / n : ℤ) : E) := by
        have hdm : a g % (n : ℤ) + (n : ℤ) * (a g / n) = a g := by
          first
            | exact Int.emod_add_ediv _ _
            | exact Int.emod_add_ediv' _ _
            | (rw [Int.emod_def]; ring)
            | exact EuclideanDomain.mod_add_div _ _
        have := congrArg (fun q : ℤ => (q : E)) hdm
        push_cast at this
        rw [this]
      rw [h2]
      ring

  have key : ∀ s s' : Set (Fin M → E), s ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s' ∈ {s : Set (Fin M → E) |
      (∃ G : AddSubgroup (Fin M → E), (G : Set (Fin M → E)) = s) ∧
        (∀ x ∈ N, (n : E) • x ∈ s) ∧ s ⊆ N} → s ∩ T = s' ∩ T → s ⊆ s' := by
    rintro s s' ⟨⟨G, hG⟩, hns, hsN⟩ ⟨⟨G', hG'⟩, hns', -⟩ heq x hx
    obtain ⟨t, ht, z, hz, rfl⟩ := hdec x (hsN hx)
    rw [← hG] at hx hns
    rw [← hG'] at hns' ⊢
    have hts : t ∈ G := by
      have := G.sub_mem hx (hns z hz)
      simpa using this
    have hts' : t ∈ s' ∩ T := heq ▸ ⟨(show t ∈ s by rw [← hG]; exact hts), ht⟩
    rw [← hG'] at hts'
    exact G'.add_mem hts'.1 (hns' z hz)
  refine Set.Finite.of_finite_image (f := fun s => s ∩ T) ?_ ?_
  · refine (hT.finite_subsets).subset ?_
    rintro _ ⟨s, -, rfl⟩
    exact Set.inter_subset_right
  · intro s hs s' hs' heq
    exact Set.Subset.antisymm (key s s' hs hs' heq) (key s' s hs' hs heq.symm)

end PI.UnitaryGroupMassFormula.UJClassFin
end
end

section

noncomputable section

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

namespace PI.UnitaryGroupMassFormula.UJClassFin

open PI.UJClassFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vinc {M : ℕ} (x : Fin M → E) : Fin M → Af F ⊗[F] E := fun i => inclR (Af F) (x i)

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def abelian₂ (L : Set (Fin M → E)) (h : HA (AF F) σ J) : Set (Fin M → E) :=
  {x | (finMat σ J h⁻¹).mulVec (vinc (F := F) x) ∈ latHat F E L}

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (e : E) :
    sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

theorem bc_mem (g : GL (Fin M) E) (hg : g ∈ UJ (σ : E →+* E) J) :
    bc (inclR (AF F)) g ∈ HR (AF F) σ J := by
  have hg' : cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E) * J * (g : Matrix (Fin M) (Fin M) E) = J := hg
  have hc : cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) =
      (cT (σ : E →+* E) (g : Matrix (Fin M) (Fin M) E)).map (inclR (AF F)) := by
    ext i j
    simp [cT, sigR_inclR]
  show cT (sigR (AF F) σ) ((g : Matrix (Fin M) (Fin M) E).map (inclR (AF F))) * J.map (inclR (AF F)) *
    (g : Matrix (Fin M) (Fin M) E).map (inclR (AF F)) = J.map (inclR (AF F))
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']

def emb : UJ (σ : E →+* E) J →* HA (AF F) σ J where
  toFun g := (⟨bc (inclR (AF F)) g.1, bc_mem σ J g.1 g.2⟩ : HR (AF F) σ J)
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

theorem emb_mem (g : UJ (σ : E →+* E) J) : emb σ J g ∈ GamG σ J := by
  have : (show HR (AF F) σ J from emb σ J g).1 ∈ HFin (AF F) σ J := ⟨g.1, g.2, rfl⟩
  exact this

theorem finMat_emb (g : UJ (σ : E →+* E) J) :
    finMat σ J (emb σ J g) = ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (Af F)) := by
  ext i j
  change (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))
      ((1 : AF F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j) =
    (1 : Af F) ⊗ₜ[F] ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) i j
  simp [Algebra.TensorProduct.map_tmul]

theorem map_mulVec_vinc (A : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    (A.map (inclR (Af F))).mulVec (vinc (F := F) x) = vinc (F := F) (A.mulVec x) := by
  ext i
  simp only [vinc]
  rw [RingHom.map_mulVec]
  rfl

theorem Lam_emb_mul (L : Set (Fin M → E)) (g : UJ (σ : E →+* E) J) (h : HA (AF F) σ J) :
    abelian₂ σ J L (emb σ J g * h) =
      (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' abelian₂ σ J L h := by
  ext x
  have hinv : (emb σ J g * h)⁻¹ = h⁻¹ * emb σ J g⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
  have h1 : ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
  have h2 : (((g⁻¹ : UJ (σ : E →+* E) J) : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *
      ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  simp only [abelian₂, Set.mem_ofPred_eq, Set.mem_image, hinv, finMat_mul, ← Matrix.mulVec_mulVec, finMat_emb,
    map_mulVec_vinc]
  constructor
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  · rintro ⟨y, hy, rfl⟩
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

def RatDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h)

def ClassFinite : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)),
    (∀ a, σ a = star a) →
    (∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a)) →
    (∀ τ : E →+* ℂ, HasSignature (J.map τ) M 0) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ L, ∀ i, IsIntegral ℤ ((c : F) • x i)) →
    (∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e → Pi.single i ((c : F) • e) ∈ L) →
    ∃ S : Set (Set (Fin M → E)), S.Finite ∧ ∀ h : HA (AF F) σ J, ∃ s ∈ S, ∃ g : UJ (σ : E →+* E) J,
      abelian₂ σ J L h = (fun x => ((g : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).mulVec x) '' s

theorem sfin_of_Lam_eq (L : Set (Fin M → E))
    (hR : ∀ (h : HA (AF F) σ J) (y : Fin M → Af F ⊗[F] E),
      (finMat σ J h⁻¹).mulVec y ∈ latHat F E L ↔ y ∈ latHat F E (abelian₂ σ J L h))
    (h h' : HA (AF F) σ J) (he : abelian₂ σ J L h = abelian₂ σ J L h') : h⁻¹ * h' ∈ SFin σ J L := by
  intro y
  rw [finMat_mul, ← Matrix.mulVec_mulVec]
  have e1 : (finMat σ J h'⁻¹).mulVec ((finMat σ J h').mulVec y) = y := by
    rw [Matrix.mulVec_mulVec, ← finMat_mul, inv_mul_cancel, finMat_one, Matrix.one_mulVec]
  rw [hR h, he, ← hR h', e1]

end PI.UnitaryGroupMassFormula.UJClassFin
end
end
