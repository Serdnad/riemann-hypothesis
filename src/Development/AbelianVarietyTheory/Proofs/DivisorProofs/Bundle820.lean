module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle009
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle790
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle791
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.FinGL.Transport

open Formalism.L2.DIV

theorem isIrreducible_comp {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ G V) (f : G' →* G) (hf : Function.Surjective f) (h : σ.IsIrreducible) :
    Representation.IsIrreducible (σ.comp f : Representation ℂ G' V) := by
  let Φ : Subrepresentation (σ.comp f : Representation ℂ G' V) ≃o Subrepresentation σ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g', rfl⟩ := hf g
        exact U.apply_mem_toSubmodule g' hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact Φ.isSimpleOrder

theorem character_coind {G G' P P' V : Type} [Group G] [Group G'] [Group P] [Group P'] [AddCommGroup V] [Module ℂ V]
    (i : P →* G) (i' : P' →* G') (σ : Representation ℂ P V) (F : G' ≃* G) (f : P' →* P) (hf : Function.Surjective f)
    (hc : ∀ p, F (i' p) = i (f p)) (x : G') :
    (Representation.coind i' (σ.comp f : Representation ℂ P' V)).character x =
      (Representation.coind i σ).character (F x) := by
  let L : Representation.coindV i σ ≃ₗ[ℂ] Representation.coindV i' (σ.comp f : Representation ℂ P' V) :=
    { toFun := fun φ => ⟨fun y => φ.1 (F y), fun p y => by
        show φ.1 (F (i' p * y)) = σ (f p) (φ.1 (F y))
        rw [map_mul, hc]
        exact φ.2 _ _⟩
      invFun := fun φ => ⟨fun y => φ.1 (F.symm y), fun p y => by
        obtain ⟨p', rfl⟩ := hf p
        show φ.1 (F.symm (i (f p') * y)) = σ (f p') (φ.1 (F.symm y))
        rw [map_mul, ← hc, MulEquiv.symm_apply_apply]
        exact φ.2 _ _⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.apply_symm_apply y))
      right_inv := fun φ => Subtype.ext (funext fun y => congrArg φ.1 (F.symm_apply_apply y)) }
  unfold Representation.character
  rw [← LinearMap.trace_conj' _ L]
  congr 1
  refine LinearMap.ext fun φ => Subtype.ext (funext fun y => ?_)
  show φ.1 (y * x) = φ.1 (F.symm (F y * F x))
  rw [← map_mul, MulEquiv.symm_apply_apply]

variable {κ κ' : Type} [Field κ] [Field κ'] {r : ℕ}

def glEquiv (e : κ' ≃+* κ) (r : ℕ) : GL (Fin r) κ' ≃* GL (Fin r) κ :=
  { Matrix.GeneralLinearGroup.map (e : κ' →+* κ) with
    invFun := Matrix.GeneralLinearGroup.map (e.symm : κ →+* κ')
    left_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    right_inv := fun g => by
      ext i j
      simp [Matrix.GeneralLinearGroup.map_apply] }

def triMap (e : κ' →+* κ) (b : Fin r → ℕ) : blockTri (κ := κ') b →* blockTri (κ := κ) b :=
  ((Matrix.GeneralLinearGroup.map e).comp (blockTri (κ := κ') b).subtype).codRestrict _ fun p i j hij => by
    have h : (p.1 : Matrix (Fin r) (Fin r) κ') i j = 0 := p.2 hij
    show e ((p.1 : Matrix (Fin r) (Fin r) κ') i j) = 0
    rw [h, map_zero]

theorem triMap_apply (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j =
      e (((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j) := rfl

theorem triMap_surjective (e : κ' ≃+* κ) (b : Fin r → ℕ) : Function.Surjective (triMap (e : κ' →+* κ) b) := fun p =>
  ⟨triMap (e.symm : κ →+* κ') b p, by
    ext i j
    simp [triMap_apply]⟩

theorem triMap_eq_one_iff (e : κ' →+* κ) (b : Fin r → ℕ) (p : blockTri (κ := κ') b) (i j : Fin r) :
    ((triMap e b p : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) i j = (1 : Matrix (Fin r) (Fin r) κ) i j ↔
      ((p : GL (Fin r) κ') : Matrix (Fin r) (Fin r) κ') i j = (1 : Matrix (Fin r) (Fin r) κ') i j := by
  have h1 : (1 : Matrix (Fin r) (Fin r) κ) i j = e ((1 : Matrix (Fin r) (Fin r) κ') i j) := by
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [triMap_apply, h1, e.injective.eq_iff]

theorem isCuspDatum_comp {V : Type} [AddCommGroup V] [Module ℂ V] (e : κ' ≃+* κ) (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := κ) b) V) (h : IsCuspDatum b σ) :
    IsCuspDatum b (σ.comp (triMap (e : κ' →+* κ) b) : Representation ℂ (blockTri (κ := κ') b) V) := by
  refine ⟨h.mono, isIrreducible_comp σ _ (triMap_surjective e b) h.irr, ?_, ?_⟩
  · intro p hp
    exact h.infl _ fun i j hij => (triMap_eq_one_iff _ b p i j).2 (hp i j hij)
  · intro S hS y hy
    refine h.cusp S hS y fun u hu => ?_
    obtain ⟨u', rfl⟩ := triMap_surjective e b u
    exact hy u' fun i j hij => hu i j fun h' => hij ((triMap_eq_one_iff _ b u' i j).1 h')

theorem isCuspProdChar_transport : ∀ (κ κ' : Type) [Field κ] [Field κ'] (e : κ ≃+* κ') (r : ℕ) (θ : GL (Fin r) κ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar θ → GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity.IsCuspProdChar
      (fun x : GL (Fin r) κ' => θ (Matrix.GeneralLinearGroup.map (e.symm : κ' →+* κ) x)) := by
  rintro κ κ' _ _ e r θ ⟨d, b, σ, hσ, hθ⟩
  refine ⟨d, b, σ.comp (triMap (e.symm : κ' →+* κ) b), isCuspDatum_comp e.symm b σ hσ, fun x => ?_⟩
  show θ _ = _
  rw [hθ]
  exact (character_coind _ _ σ (glEquiv e.symm r) _ (triMap_surjective e.symm b) (fun _ => rfl) x).symm

end GlobalTheory.FinGL.Transport
end
end

section

noncomputable section

namespace GlobalTheory.FinGL.MultSharpPf

open GlobalTheory.FinGL Formalism.L2.DIV Module NumberField GlobalTheory.IndefiniteRowSideFullHecke.CuspidalProductMultiplicity

def PlaceBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ →
    ∀ ρ k : ℕ, 1 ≤ k → ρ + k + 1 ≤ r → r ≤ Fintype.card F →
      (Fintype.card F : ℝ) ^ k * (1 - 1 / (Fintype.card F : ℝ)) ≤ (nPos ψ (parInd b σ) ρ k : ℝ) ∧
      (nPos ψ (parInd b σ) ρ k : ℝ) ≤ (Fintype.card F : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Fintype.card F : ℝ))

theorem mem_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G) (χ : G → ℂ)
    (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem card_mul_finrank_eig {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (τ : Representation ℂ G V) (P : Subgroup G) [Fintype P] (ψ : G → ℂ) (h1 : ψ 1 = 1)
    (hm : ∀ x ∈ P, ∀ y ∈ P, ψ (x * y) = ψ x * ψ y) :
    (Fintype.card P : ℂ) * (finrank ℂ (eig τ (P : Set G) ψ) : ℂ) =
      ∑ h : P, LinearMap.trace ℂ V (τ h) * (ψ h)⁻¹ := by
  have hc : (Fintype.card P : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h0 : ∀ x ∈ P, ψ x ≠ 0 := fun x hx e => by
    have := hm x hx x⁻¹ (P.inv_mem hx)
    rw [mul_inv_cancel, h1, e, zero_mul] at this
    exact one_ne_zero this
  set e : V →ₗ[ℂ] V := (Fintype.card P : ℂ)⁻¹ • ∑ h : P, (ψ h)⁻¹ • (τ h : V →ₗ[ℂ] V) with he
  have hp : LinearMap.IsProj (eig τ (P : Set G) ψ) e := by
    constructor
    · intro v
      rw [mem_eig]
      intro g hg
      have hg' : g ∈ P := hg

      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply, map_smul, map_sum]
      rw [smul_comm (ψ g)]
      congr 1
      rw [Finset.smul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft (⟨g, hg'⟩ : P)) _ _ fun x => ?_
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hm g hg' x x.2, smul_smul, mul_inv, ← mul_assoc, mul_inv_cancel₀ (h0 g hg'), one_mul]
    · intro v hv
      rw [mem_eig] at hv
      simp only [he, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl (g := fun _ => v) fun x _ => by
        rw [hv x x.2, smul_smul, inv_mul_cancel₀ (h0 x x.2), one_smul]]
      rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

  rw [← hp.trace, he, map_smul, map_sum, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

variable {E : Type} [Field E] [NumberField E]

def piEquiv {Pg : Finset (Pl E)} {r : ℕ} (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) :
    (Subgroup.pi Set.univ Hl : Subgroup (G0 Pg r)) ≃ ∀ PP : ↥Pg, Hl PP where
  toFun x PP := LevelP.prj Hl PP x
  invFun y := ⟨fun PP => y PP, fun PP _ => (y PP).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem levelMult_ofLocal {K : Type} [Field K] (s : K →+* ℂ) {Pg : Finset (Pl E)} {r : ℕ}
    (Hl : ∀ PP : ↥Pg, Subgroup (GL (Fin r) (kP PP.1))) [∀ PP, Fintype (Hl PP)] (cl : ∀ PP : ↥Pg, Hl PP →* Kˣ)
    (χ : G0 Pg r → K) (θ : ∀ PP : ↥Pg, GL (Fin r) (kP PP.1) → ℂ) (hχ : ∀ x, s (χ x) = ∏ PP : ↥Pg, θ PP (x PP))
    (n : ↥Pg → ℕ)
    (hn : ∀ PP, (Fintype.card (Hl PP) : ℂ) * (n PP : ℂ) = ∑ h : Hl PP, θ PP h * (s (cl PP h : K))⁻¹) :
    levelMult (LevelP.ofLocal Hl cl) χ = ((∏ PP, n PP : ℕ) : K) := by
  classical
  apply s.injective
  unfold levelMult

  rw [map_mul, map_inv₀, map_natCast, map_natCast, map_sum]
  have hcard : Nat.card (LevelP.ofLocal Hl cl).H = ∏ PP, Fintype.card (Hl PP) := by
    rw [← Fintype.card_pi, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (piEquiv Hl)
  have hne : (∏ PP, (Fintype.card (Hl PP) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun PP _ => by exact_mod_cast Fintype.card_ne_zero
  rw [hcard, Nat.cast_prod, Nat.cast_prod, inv_mul_eq_iff_eq_mul₀ hne, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun PP _ => hn PP, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine @Fintype.sum_equiv _ _ _ (_) _ _ (piEquiv Hl) _ _ fun x => ?_
  rw [map_mul, hχ, Finset.prod_mul_distrib, Finset.prod_inv_distrib, Units.val_inv_eq_inv_val, map_inv₀]
  congr 2
  show s ((((∏ PP : ↥Pg, (cl PP).comp (LevelP.prj Hl PP)) x : Kˣ)) : K) = _
  rw [MonoidHom.finsetProd_apply, Units.coe_prod, map_prod]
  rfl

theorem edgeSum_sup_eq {κ : Type} [CommRing κ] {r k : ℕ} {g : GL (Fin r) κ} (hg : g ∈ unipCol κ r 0 k) :
    edgeSum supEdge g = edgeSum (symEdge 0 k) g := by
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h1 : supEdge i j <;> by_cases h2 : symEdge 0 k i j
  · rw [if_pos h1, if_pos h2]
  · rw [if_pos h1, if_neg h2]
    unfold supEdge at h1
    unfold symEdge at h2
    exact hg.2 i j (Nat.zero_le _) (by omega) (by omega)
  · unfold supEdge at h1
    unfold symEdge at h2
    omega
  · rw [if_neg h1, if_neg h2]

theorem addCharHom_sym {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r ρ k : ℕ} (ψ : AddChar κ K) (h : unipSym κ r ρ k) :
    (addCharHom ψ (symHom κ r ρ k) h : K) = ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ)) := rfl

theorem addCharHom_first {κ : Type} [CommRing κ] {K : Type} [CommRing K] {r k : ℕ} (ψ : AddChar κ K) (h : unipCol κ r 0 k) :
    ((addCharHom ψ (supHom κ r)).comp (Subgroup.inclusion (unipCol_le r 0 k)) h : K) =
      ψ (edgeSum (symEdge 0 k) (h : GL (Fin r) κ)) := by
  rw [← edgeSum_sup_eq h.2]
  rfl

theorem place (H : PlaceBound) {κ : Type} [Field κ] [Finite κ] {K : Type} [Field K] (s : K →+* ℂ) (ψ : AddChar κ K)
    (hψ : ψ ≠ 1) {r ρ k : ℕ} (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hq : r ≤ Nat.card κ) (θ : GL (Fin r) κ → ℂ)
    (hθ : IsCuspProdChar θ) [Fintype (unipSym κ r ρ k)] :
    ∃ n : ℕ, (Fintype.card (unipSym κ r ρ k) : ℂ) * (n : ℂ) =
        ∑ h : unipSym κ r ρ k, θ h * (s (ψ (edgeSum (symEdge ρ k) (h : GL (Fin r) κ))))⁻¹ ∧
      (Nat.card κ : ℝ) ^ k * (1 - 1 / (Nat.card κ : ℝ)) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (Nat.card κ : ℝ) ^ k * (1 + (2 * (r : ℝ) - 1) / (Nat.card κ : ℝ)) := by
  obtain ⟨d, b, σ, hσ, hθ⟩ := hθ
  letI : Fintype κ := Fintype.ofFinite κ
  set φ : AddChar κ ℂ := s.toMonoidHom.compAddChar ψ with hφ
  have hφa : ∀ x, φ x = s (ψ x) := fun _ => rfl
  have hφ1 : φ ≠ 1 := fun e => hψ (by
    ext x
    apply s.injective
    rw [← hφa, e]; simp)
  rw [Nat.card_eq_fintype_card] at hq ⊢
  refine ⟨nPos φ (parInd b σ) ρ k, ?_, H κ φ hφ1 r _ b σ hσ ρ k hk hr hq⟩
  unfold nPos
  rw [card_mul_finrank_eig (parInd b σ) (unipSym κ r ρ k) (fun g => φ (edgeSum (symEdge ρ k) g))]
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [hθ]; rfl
  · have := (symHom κ r ρ k).map_one
    have h2 : edgeSum (symEdge ρ k) (1 : GL (Fin r) κ) = 0 := this
    simp only [h2, AddChar.map_zero_eq_one]
  · intro x hx y hy
    have := (symHom κ r ρ k).map_mul ⟨x, hx⟩ ⟨y, hy⟩
    have h2 : edgeSum (symEdge ρ k) (x * y) = edgeSum (symEdge ρ k) x + edgeSum (symEdge ρ k) y := this
    simp only [h2, AddChar.map_add_eq_mul]

theorem places (H : PlaceBound) {K : Type} [Field K] (s : K →+* ℂ) (Pg : Finset (Pl E)) (f g r ρ k c : ℕ) (hc : c = ρ + k)
    (ψ : ∀ PP : Pl E, AddChar (kP PP) K) (hf : Pg.card = 2 * f) (hk : 1 ≤ k) (hr : ρ + k + 1 ≤ r) (hg : 0 < g)
    (hfg : 4 * f * r ≤ g) (hq : ∀ PP ∈ Pg, g ≤ Nat.card (kP PP)) (hψ : IsGenericPsi Pg ψ)
    (cl : ∀ PP : ↥Pg, unipCol (kP PP.1) r ρ c →* Kˣ)
    (hcl : ∀ PP h, (cl PP h : K) = ψ PP.1 (edgeSum (symEdge ρ k) (h : GL (Fin r) (kP PP.1))))
    (χ : G0 Pg r → K) (hχ : IsProdCuspChar s Pg r χ) :
    MultNear (LevelP.ofLocal (fun PP => unipCol (kP PP.1) r ρ c) cl) χ (nbar Pg k) (8 * f * r / g) := by
  subst hc
  obtain ⟨θ, hθ, hχ⟩ := hχ
  have hfin : ∀ PP : ↥Pg, Finite (kP PP.1) := fun PP => finite_kP PP.1
  letI : ∀ PP : ↥Pg, Fintype (unipCol (kP PP.1) r ρ (ρ + k)) := fun PP => Fintype.ofFinite _
  have hrq : ∀ PP : ↥Pg, r ≤ Nat.card (kP PP.1) := fun PP => by
    have h1 : 0 < Pg.card := Finset.card_pos.2 ⟨PP.1, PP.2⟩
    have h2 : 1 ≤ 4 * f := by omega
    exact le_trans (le_trans (Nat.le_mul_of_pos_left r h2) hfg) (hq PP.1 PP.2)
  have hloc := fun PP : ↥Pg => @place H (kP PP.1) (Ideal.Quotient.field PP.1.asIdeal) (hfin PP) K _ s (ψ PP.1)
    (hψ PP.1 PP.2) r ρ k hk hr (hrq PP) (θ PP) (hθ PP) (this PP)
  choose n hn hb using hloc
  refine ⟨∏ PP, n PP, levelMult_ofLocal s _ cl χ θ hχ n fun PP => ?_, ?_⟩
  · simp only [hcl]
    exact hn PP
  · have := Formalism.BranchingDeterminantCap.multiplicity_product ↥Pg (fun PP => (Nat.card (kP PP.1) : ℝ)) (fun PP => (n PP : ℝ)) k f r g
      (by rw [Fintype.card_coe, hf]; push_cast; rfl) (by exact_mod_cast (by omega : 1 ≤ r)) (by exact_mod_cast hg)
      (fun PP => by exact_mod_cast hq PP.1 PP.2) (by exact_mod_cast hfg) hb
    have e : (nbar Pg k : ℝ) = ∏ PP : ↥Pg, (Nat.card (kP PP.1) : ℝ) ^ k := by
      unfold nbar
      rw [← Finset.prod_coe_sort Pg]; push_cast; rfl
    rw [e, Nat.cast_prod, abs_le]
    constructor <;> linarith [this.1, this.2]

theorem multSharp_of_placeBound (H : PlaceBound) : MultSharp := by
  intro E _ _ K _ _ s Pg f g r ρ k ψ hf hk hr hg hfg hq hψ χ hχ
  constructor
  · unfold PsharpSym
    exact places H s Pg f g r ρ k (ρ + k) rfl ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => addCharHom (ψ PP.1) (symHom (kP PP.1) r ρ k)) (fun PP h => addCharHom_sym _ h) χ hχ
  · unfold Psharp
    exact places H s Pg f g r 0 k k (Nat.zero_add k).symm ψ hf hk (by omega) hg hfg hq hψ
      (fun PP => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (Subgroup.inclusion (unipCol_le r 0 k)))
      (fun PP h => addCharHom_first _ h) χ hχ

end GlobalTheory.FinGL.MultSharpPf
end
end

section

noncomputable section

namespace GlobalTheory.CuspidalIdempotentCharacters

open Formalism.L2.DIV GlobalTheory.FinGL NumberField

theorem isIndCuspChar_iff {E : Type} [Field E] [NumberField E] (Pg : Finset (Pl E)) (r : ℕ) {K : Type} [Field K]
    (s : K →+* ℂ) (χ : G0 Pg r → K) :
    GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.IsIndCuspChar Pg r s χ ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar Pg r s χ := by
  constructor
  · rintro ⟨b, V, i1, i2, i3, σ, hc, hχ⟩
    exact ⟨_, fun PP => ⟨b PP, V PP, i1 PP, i2 PP, i3 PP, σ PP, hc PP, fun _ => rfl⟩, hχ⟩
  · rintro ⟨θ, hθ, hχ⟩
    choose b V i1 i2 i3 σ hc ht using hθ
    exact ⟨b, V, i1, i2, i3, σ, hc, fun g => (hχ g).trans (Finset.prod_congr rfl fun PP _ => ht PP (g PP))⟩

theorem sum_eq_lvlSum {E : Type} [Field E] [NumberField E] {Pg : Finset (Pl E)} {r : ℕ} {K : Type} [Field K]
    (P : LevelP Pg r K) (χ : G0 Pg r → K) (i : Fintype P.H) :
    ∑ h : P.H, χ (h : G0 Pg r) * (((P.chi h)⁻¹ : Kˣ) : K) = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum P χ := by
  obtain rfl : i = GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH P := Subsingleton.elim _ _
  rfl

theorem genericMultOne_iff : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne ↔ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector
  refine forall_congr' fun E => forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun Pg =>
    forall_congr' fun r => forall_congr' fun K => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun s => forall_congr' fun ψ => forall_congr' fun _ => forall_congr' fun χ =>
    imp_congr (isIndCuspChar_iff Pg r s χ) ?_
  rw [← sum_eq_lvlSum (P0 Pg r ψ) χ]

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

theorem eps_eq_lvlIdem (H : Subgroup G) (ψ : H →* Kˣ) :
    Formalism.MainNotions.PrimeDegreeVariant.eps (⟨H, ψ⟩ : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) = lvlIdem H ψ := by
  classical
  unfold Formalism.MainNotions.PrimeDegreeVariant.eps lvlIdem
  rw [Finset.smul_sum]
  symm
  refine Fintype.sum_of_injective (fun h : H => (h : G)) Subtype.val_injective _ _ ?_ ?_
  · intro x hx
    have : x ∉ H := fun h => hx ⟨⟨x, h⟩, rfl⟩
    simp [this]
  · intro h
    simp [map_inv]

variable {W : Type} [AddCommGroup W] [Module K W]

theorem asAlgebraHom_lvlIdem (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) [Fintype H] :
    τ.asAlgebraHom (lvlIdem H ψ) = (Nat.card H : K)⁻¹ • ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) := by
  unfold lvlIdem

  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr (by congr!) fun h _ => ?_
  rw [Representation.asAlgebraHom_single, smul_smul, map_inv]

theorem isIdempotentElem_lvlIdem [CharZero K] (τ : Representation K G W) (H : Subgroup G) (ψ : H →* Kˣ) :
    IsIdempotentElem (τ.asAlgebraHom (lvlIdem H ψ)) := by
  classical
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  set T : Module.End K W := ∑ h : H, (((ψ h)⁻¹ : Kˣ) : K) • τ (h : G) with hT
  have h1 : ∀ a : H, ((((ψ a)⁻¹ : Kˣ) : K) • τ (a : G)) * T = T := by
    intro a
    rw [hT, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun h => ?_
    simp [smul_smul, mul_comm]
  have h2 : T * T = (Nat.card H : K) • T := by
    conv_lhs => rw [hT, Finset.sum_mul, ← hT]
    rw [Finset.sum_congr rfl fun a _ => h1 a]
    simp [Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [IsIdempotentElem, asAlgebraHom_lvlIdem, ← hT, smul_mul_smul_comm, h2, smul_smul, mul_assoc,
    inv_mul_cancel₀ hc, mul_one]

theorem finrank_eq_one_iff [CharZero K] [FiniteDimensional K W] (τ : Representation K G W) (H : Subgroup G)
    (ψ : H →* Kˣ) [Fintype H] :
    Module.finrank K (LinearMap.range (τ.asAlgebraHom (lvlIdem H ψ))) = 1 ↔
      ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) = (Nat.card H : K) := by
  have hc : (Nat.card H : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := H)).ne'
  have h := (LinearMap.IsIdempotentElem.isProj_range _ (isIdempotentElem_lvlIdem τ H ψ)).trace
  have e : LinearMap.trace K W (τ.asAlgebraHom (lvlIdem H ψ)) =
      (Nat.card H : K)⁻¹ * ∑ h : H, LinearMap.trace K W (τ (h : G)) * (((ψ h)⁻¹ : Kˣ) : K) := by

    rw [asAlgebraHom_lvlIdem, map_smul, map_sum, smul_eq_mul]
    simp [mul_comm]
  rw [← Nat.cast_eq_one (R := K), ← h, e, inv_mul_eq_one₀ hc, eq_comm]

end Idem

end GlobalTheory.CuspidalIdempotentCharacters
end
end

section

open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspRep


open Finset in
theorem zalg_eq_adjoin_finite_caps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ),
    ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧
      Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  intro E _ _ _ b
  classical
  refine ⟨univ.image (fun p : (E →+* ℂ) × Fin (b + 1) => cap (a := b) p.1 ((p.2 : ℕ) : ℂ)), ?_, ?_⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := mem_image.1 ht
    exact ⟨p.1, _, rfl⟩
  · apply le_antisymm
    · unfold Zalg
      rw [Algebra.adjoin_le_iff]
      rintro z ⟨τ, u, rfl⟩
      obtain ⟨w, hw⟩ := cap_eq_sum_nodes E b τ u
      rw [hw]
      refine Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨(τ, j), rfl⟩
    · unfold Zalg
      apply Algebra.adjoin_mono
      intro t ht
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht
      obtain ⟨p, rfl⟩ := ht
      exact ⟨p.1, _, rfl⟩

end GlobalTheory.CuspRep

end
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

theorem _root_.GlobalTheory.T.weierstrassTorsion_qExpansion_integral : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (N : ℕ) [NeZero N] (M : ℕ) (x : Fin 2 → ZMod N), ¬ l ∣ M → M • x = 0 → x ≠ 0 → QAll (Sz l lam 0) N (wB N x) ∧ QAll (Sz l lam 0) N (wpd N x) := by
  first | exact @GlobalTheory.WpFam.ExpansionIntegral.main | exact GlobalTheory.WpFam.ExpansionIntegral.main | (intros; apply GlobalTheory.WpFam.ExpansionIntegral.main <;> assumption)
end
