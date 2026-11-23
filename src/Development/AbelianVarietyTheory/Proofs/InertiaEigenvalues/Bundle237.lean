module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle232
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle218
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle007
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SemisimplificationConstituents
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle008
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle224
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.FieldTheory.Separable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatesSeparableMatrixCompactModCentralizer
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Polynomial

noncomputable section
namespace GlobalTheory.ConsCompare

section Factors
open GlobalTheory.AdmLoc
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

theorem finiteLength_of_finiteDimensional (k : Type) [Field k] [Algebra k A] (M : Type) [AddCommGroup M]
    [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M] : IsFiniteLength A M := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩

theorem exists_semisimple_sameFactors : ∀ (d : ℕ) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M], Module.finrank k M = d →
    ∃ (S : Type) (_ : AddCommGroup S) (_ : Module k S) (_ : Module A S) (_ : IsScalarTower k A S)
      (_ : FiniteDimensional k S), IsSemisimpleModule A S ∧ SameFactors A M S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ _ _ hd
  have hfl := finiteLength_of_finiteDimensional (A := A) k M
  rcases subsingleton_or_nontrivial M with h0 | h0
  · exact ⟨M, _, _, _, inferInstance, inferInstance, (isSemisimpleModule_iff A M).2
      (have := (Submodule.subsingleton_iff A).2 h0; Subsingleton.instComplementedLattice),
      SameFactors.refl hfl⟩
  · haveI : IsNoetherian A M := isNoetherian_of_tower k inferInstance
    obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left bot_ne_top
    have hlt : Module.finrank k N < d := by
      rw [← hd]
      exact Submodule.finrank_lt (s := N.restrictScalars k) fun h => hN.1 (by simpa using h)
    obtain ⟨S, _, _, _, _, _, hS, hf⟩ := ih _ hlt N rfl
    haveI : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
    exact ⟨S × (M ⧸ N), _, _, _, inferInstance, inferInstance,
      isSemisimpleModule_of_isSemisimpleModule_submodule' (p := fun b : Bool =>
        cond b (LinearMap.range (LinearMap.inl A S (M ⧸ N))) (LinearMap.range (LinearMap.inr A S (M ⧸ N))))
        (by rintro (_ | _) <;> exact IsSemisimpleModule.range _)
        (by rw [iSup_bool_eq]; exact LinearMap.sup_range_inl_inr),
      (SameFactors.sub_prod_quot hfl N).trans
        (hf.prod (SameFactors.refl (finiteLength_of_finiteDimensional k _)))⟩

theorem cpOn_eq_of_sameFactors (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M']
    [IsScalarTower k A M'] [FiniteDimensional k M'] (h : SameFactors A M M') : cpOn k a M = cpOn k a M' := by
  obtain ⟨s, t, h1, h2, h3, h4, f, hf⟩ := h
  rw [cpOn_series _ s h1 h2, cpOn_series _ t h3 h4]
  exact Fintype.prod_equiv f _ _ fun j => cpOn_congr _ (hf j).some

variable {Γ : Type} [Group Γ]

def repOf (k Γ S : Type) [Field k] [Group Γ] [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] : Representation k Γ S :=
  (Algebra.lsmul k k S : MonoidAlgebra k Γ →ₐ[k] Module.End k S).toMonoidHom.comp (MonoidAlgebra.of k Γ)

theorem isSS_repOf {S : Type} [AddCommGroup S] [Module k S] [Module (MonoidAlgebra k Γ) S]
    [IsScalarTower k (MonoidAlgebra k Γ) S] [IsSemisimpleModule (MonoidAlgebra k Γ) S] :
    IsSS (repOf k Γ S) := fun W hW => by
  let W₁ : Submodule (MonoidAlgebra k Γ) S :=
    { W.toAddSubmonoid with
      smul_mem' := fun a v hv => by
        induction a using MonoidAlgebra.induction_on with
        | of g => exact hW g v hv
        | add a b ha hb => rw [add_smul]; exact W.add_mem ha hb
        | smul c a ha => rw [smul_assoc]; exact W.smul_mem c ha }
  obtain ⟨W₂, h⟩ := exists_isCompl W₁
  refine ⟨W₂.restrictScalars k, fun g v hv => W₂.smul_mem (MonoidAlgebra.of k Γ g) hv, ?_⟩
  exact (Submodule.isCompl_restrictScalars_iff k (s := W₁)).2 h

theorem sameSS_of_charpoly_eq (hBN : GlobalTheory.ConstituentsCompare.BrauerNesbitt) {V W : Type} [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k Γ V) (σ : Representation k Γ W)
    (h : ∀ g, LinearMap.charpoly (ρ g) = LinearMap.charpoly (σ g)) : GlobalTheory.IndefiniteRowSideFullHecke.CharPolyRootsConstruction.SameSS ρ σ := by
  have : FiniteDimensional k ρ.asModule := inferInstanceAs (FiniteDimensional k V)
  have : FiniteDimensional k σ.asModule := inferInstanceAs (FiniteDimensional k W)
  have e1 : ∀ g, LinearMap.charpoly (ρ g) = cpOn k (MonoidAlgebra.of k Γ g) ρ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj ρ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  have e2 : ∀ g, LinearMap.charpoly (σ g) = cpOn k (MonoidAlgebra.of k Γ g) σ.asModule := fun g => by
    unfold cpOn
    rw [← LinearEquiv.charpoly_conj σ.asModuleEquiv]
    congr 1
    ext v
    simp [LinearEquiv.conj_apply]
    rfl
  obtain ⟨S, _, _, _, _, _, hS, hf⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ ρ.asModule rfl
  obtain ⟨S', _, _, _, _, _, hS', hf'⟩ :=
    exists_semisimple_sameFactors (k := k) (A := MonoidAlgebra k Γ) _ σ.asModule rfl
  obtain ⟨e, he⟩ := GlobalTheory.brauerNesbitt_abstract_of_matrix hBN (repOf k Γ S) (repOf k Γ S') isSS_repOf isSS_repOf
    fun g => ((cpOn_eq_of_sameFactors _ hf).symm.trans ((e1 g).symm.trans ((h g).trans (e2 g)))).trans
      (cpOn_eq_of_sameFactors _ hf')
  let e' : S ≃ₗ[MonoidAlgebra k Γ] S' :=
    { e.toAddEquiv with
      map_smul' := fun a v => by
        show e (a • v) = a • e v
        induction a using MonoidAlgebra.induction_on with
        | of g => exact he g v
        | add a b ha hb => rw [add_smul, add_smul, map_add (f := _), ha, hb]
        | smul c a ha => rw [smul_assoc, smul_assoc, map_smul, ha] }
  exact (hf.trans (SameFactors.of_equiv hf.finiteLength_right e')).trans hf'.symm

end Factors

section Distinct
open Matrix

end Distinct

section BaseChange
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A B : Type} [Group Γ] [CommRing A] [CommRing B] {n r t : ℕ}

variable [Algebra A B]

variable [IsDomain A] [IsDomain B]

variable [IsLocalRing A] [IsLocalRing B]

end BaseChange

end GlobalTheory.ConsCompare
end
end

section

open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.StableLattice

theorem exists_matrix_of_saturated {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {n : ℕ} (L : Submodule O (Fin n → O))
    (hL : ∀ (c : O) (v : Fin n → O), c ≠ 0 → c • v ∈ L → v ∈ L) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) O) (P : Matrix (Fin m) (Fin n) O),
      P * B = 1 ∧ ∀ v, v ∈ L ↔ B.mulVec (P.mulVec v) = v := by
  have : Module.IsTorsionFree O ((Fin n → O) ⧸ L) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x hx
    obtain ⟨v, rfl⟩ := L.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hL c v hc hx
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  have hs' : ∀ x, L.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  let p : (Fin n → O) →ₗ[O] L := LinearMap.codRestrict L (LinearMap.id - s ∘ₗ L.mkQ) (by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self])
  have hp : ∀ x : L, p x = x := by
    intro x
    apply Subtype.ext
    have : L.mkQ (x : Fin n → O) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, this, map_zero, sub_zero]
  let e := (Module.finBasis O L).equivFun
  refine ⟨Module.finrank O L, LinearMap.toMatrix' (L.subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ p), ?_, fun v => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hp, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    constructor
    · intro hv
      exact congrArg Subtype.val (hp ⟨v, hv⟩)
    · intro hv
      rw [← hv]
      exact (p v).2

theorem exists_integral_model (O Γ : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Group Γ] [TopologicalSpace Γ] (n a : ℕ)
    (r : Γ →* GL (Fin n) O) (hr : LatticeContinuous r)
    (W : Submodule (FractionRing O) (Fin n → FractionRing O))
    (hW : ∀ g, ∀ v ∈ W, fracRep r g v ∈ W) (ha : Module.finrank (FractionRing O) W = a) :
    ∃ (ρ : Γ →* GL (Fin a) O)
      (k : (Fin a → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O)),
      LatticeContinuous ρ ∧ Function.Injective k ∧ LinearMap.range k = W ∧
        ∀ g v, fracRep r g (k v) = k (fracRep ρ g v) := by
  set φ := algebraMap O (FractionRing O) with hφ
  have hφi : Function.Injective φ := IsFractionRing.injective O (FractionRing O)
  let c : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  have hc : ∀ v, c v = φ ∘ v := fun v => rfl
  let L : Submodule O (Fin n → O) := (W.restrictScalars O).comap c
  have hLm : ∀ v, v ∈ L ↔ φ ∘ v ∈ W := fun v => Iff.rfl
  have hsm : ∀ (x : O) (v : Fin n → O), φ ∘ (x • v) = φ x • (φ ∘ v) := by
    intro x v; funext i; simp
  obtain ⟨m, B, P, hPB, hL⟩ := exists_matrix_of_saturated L (by
    intro x v hx hv
    rw [hLm, hsm] at hv
    rw [hLm]
    exact (W.smul_mem_iff (by simpa using (map_ne_zero_iff φ hφi).2 hx)).1 hv)
  have hfr : ∀ {b : ℕ} (σ : Γ →* GL (Fin b) O) g v, fracRep σ g v =
      (((σ g : GL (Fin b) O) : Matrix (Fin b) (Fin b) O).map φ).mulVec v := fun σ g v => rfl
  have hmv : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) O) (v : Fin q → O),
      φ ∘ A.mulVec v = (A.map φ).mulVec (φ ∘ v) := by
    intro p q A v; funext i; exact RingHom.map_mulVec φ A v i
  have hBL : ∀ u, B.mulVec u ∈ L := by
    intro u
    rw [hL, Matrix.mulVec_mulVec u P B, hPB, Matrix.one_mulVec]
  have hst : ∀ g, B * (P * (r g : Matrix (Fin n) (Fin n) O) * B) =
      (r g : Matrix (Fin n) (Fin n) O) * B := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : (r g : Matrix (Fin n) (Fin n) O).mulVec (B.mulVec (Pi.single j 1)) ∈ L := by
      rw [hLm, hmv, ← hfr]
      exact hW g _ ((hLm _).1 (hBL _))
    have h2 := (hL _).1 h1
    simp only [← Matrix.mulVec_mulVec]
    exact h2
  let k : (Fin m → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O) :=
    (B.map φ).mulVecLin
  have hk : ∀ v, k v = (B.map φ).mulVec v := fun v => rfl
  have hki : Function.Injective k := by
    apply Function.LeftInverse.injective (g := (P.map φ).mulVec)
    intro v
    rw [hk, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero φ) (map_one φ),
      Matrix.one_mulVec]
  have hkr : LinearMap.range k = W := by
    apply le_antisymm
    · rw [Matrix.range_mulVecLin, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := (hLm _).1 (hBL (Pi.single j 1))
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro w hw
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
        (nonZeroDivisors O) (S := FractionRing O) w
      choose v hv using hd
      have hd0 : φ (d : O) ≠ 0 := (map_ne_zero_iff φ hφi).2 (nonZeroDivisors.coe_ne_zero d)
      have hvw : φ ∘ v = φ (d : O) • w := by
        funext i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        rw [hφ, hv i, Algebra.smul_def]
      have hvL : v ∈ L := by rw [hLm, hvw]; exact W.smul_mem _ hw
      rw [← (LinearMap.range k).smul_mem_iff hd0, ← hvw, ← (hL v).1 hvL, hmv]
      exact ⟨_, hk _⟩
  obtain rfl : m = a := by
    rw [← ha, ← hkr, LinearMap.finrank_range_of_inj hki, Module.finrank_fin_fun]
  let ρ₀ : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => P * (r g : Matrix (Fin n) (Fin n) O) * B
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, hPB]
      map_mul' := by
        intro g h
        rw [Matrix.mul_assoc (P * _) B, hst, map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc] }
  refine ⟨ρ₀.toHomUnits, k, ?_, hki, hkr, fun g v => ?_⟩
  · exact (continuous_const.matrix_mul hr).matrix_mul continuous_const
  · rw [hfr, hfr, hk, hk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← Matrix.map_mul, ← hst g]
    rfl

end GlobalTheory.StableLattice
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimplificationCharpoly

private theorem charpoly_eq_of_filtration_graded_eq {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (G : ℕ → Submodule k V)
      (f g : Module.End k V), Monotone G → G 0 = ⊥ → G n = ⊤ → (∀ i, ∀ x ∈ G i, f x ∈ G i) →
      (∀ i, ∀ x ∈ G (i + 1), g x - f x ∈ G i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  induction n with
  | zero =>
    intro V _ _ _ G f g _ h0 hn _ _
    have hV : ∀ x : V, x = 0 := by
      intro x
      have hx : x ∈ G 0 := by rw [hn]; exact Submodule.mem_top
      rw [h0] at hx
      exact (Submodule.mem_bot k).mp hx
    have hfg : f = g := by
      ext x
      rw [hV x, map_zero, map_zero]
    rw [hfg]
  | succ n ih =>
    intro V _ _ _ G f g hmono h0 hn hf hd

    have hg : ∀ i, ∀ x ∈ G i, g x ∈ G i := by
      intro i x hx
      cases i with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx, map_zero]
        exact Submodule.zero_mem _
      | succ j =>
        have e : g x = f x + (g x - f x) := by abel
        rw [e]
        exact Submodule.add_mem _ (hf _ x hx) (hmono (Nat.le_succ j) (hd j x hx))
    set A := G n with hA
    rw [GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A f (hf n),
      GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ A g (hg n)]
    congr 1
    ·
      refine ih (fun i => (G i).comap A.subtype) (f.restrict (hf n)) (g.restrict (hg n))
        (fun i j hij => Submodule.comap_mono (hmono hij)) ?_ ?_ ?_ ?_
      · rw [h0, Submodule.comap_bot, Submodule.ker_subtype]
      · exact Submodule.comap_subtype_self A
      · intro i x hx
        exact hf i x hx
      · intro i x hx
        exact hd i x hx
    ·
      congr 1
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.mapQ_apply]
      rw [Submodule.Quotient.eq]
      have hx : x ∈ G (n + 1) := by rw [hn]; exact Submodule.mem_top
      have := hd n x hx
      rw [← neg_mem_iff, neg_sub] at this
      exact this

theorem charpoly_eq_of_filtration {k : Type} [Field k] (n : ℕ) :
    ∀ {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (F : ℕ → Submodule k V)
      (f g : Module.End k V), F 0 = ⊥ → F n = ⊤ → (∀ i, ∀ x ∈ F i, f x ∈ F i) →
      (∀ i, ∀ x ∈ F (i + 1), g x - f x ∈ F i) → LinearMap.charpoly f = LinearMap.charpoly g := by
  intro V _ _ _ F f g h0 hn hf hd

  refine charpoly_eq_of_filtration_graded_eq n (fun i => partialSups F i) f g (partialSups F).monotone ?_ ?_ ?_ ?_
  · simp only [partialSups_zero, h0]
  · exact eq_top_iff.mpr (hn ▸ le_partialSups F n)
  · intro i
    have hle : partialSups F i ≤ (partialSups F i).comap f := by
      refine partialSups_le F i _ (fun j hj x hx => ?_)
      exact le_partialSups_of_le F hj (hf j x hx)
    exact fun x hx => hle hx
  · intro i
    have hle : partialSups F (i + 1) ≤ (partialSups F i).comap (g - f) := by
      refine partialSups_le F (i + 1) _ (fun j hj x hx => ?_)
      cases j with
      | zero =>
        rw [h0] at hx
        rw [(Submodule.mem_bot k).mp hx]
        exact Submodule.zero_mem _
      | succ m =>
        exact le_partialSups_of_le F (Nat.succ_le_succ_iff.mp hj) (hd m x hx)
    exact fun x hx => hle hx

theorem charpoly_eq : ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (s : Representation k Γ W) (ρ : Representation k Γ V),
    GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf s ρ →
      ∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (ρ g) := by
  intro k Γ _ _ W _ _ _ V _ _ _ s ρ hss g
  unfold GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsSemisimplificationOf at hss
  obtain ⟨-, m, Ws, e, hst, hint, hρ⟩ := hss
  have hsj : ∀ j, ∀ x ∈ Ws j, s g x ∈ Ws j := by
    intro j x hx
    have h := hst j
    unfold Stable at h
    exact h g x hx

  let H : ℕ → Submodule k W := fun i => ⨆ (j : Fin m) (_ : (j : ℕ) < i), Ws j
  have hH : ∀ i, ∀ x ∈ H i, s g x ∈ H i := by
    intro i
    have hle : H i ≤ (H i).comap (s g) :=
      iSup₂_le fun j hj x hx =>
        (le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j hj) (hsj j x hx)
    exact fun x hx => hle hx
  rw [← e.charpoly_conj (s g)]
  refine charpoly_eq_of_filtration m (fun i => (H i).map (e : W →ₗ[k] V)) (e.conj (s g)) (ρ g)
    ?_ ?_ ?_ ?_
  · have h0 : H 0 = ⊥ := by simp [H]
    simp only [h0, Submodule.map_bot]
  · have hm : H m = ⊤ := by
      rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
      exact iSup_le fun j => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < m) => Ws j) j j.isLt
    simp only [hm, Submodule.map_top, LinearEquiv.range]
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx ⊢
    simpa [LinearEquiv.conj_apply] using hH i _ hx
  · intro i x hx
    rw [Submodule.mem_map_equiv] at hx
    have hle : H (i + 1) ≤ ((H i).map (e : W →ₗ[k] V)).comap
        ((ρ g - e.conj (s g)) ∘ₗ (e : W →ₗ[k] V)) := by
      refine iSup₂_le fun j hj v hv => ?_
      have hsub : (⨆ j' ∈ Set.Iio j, Ws j') ≤ H i :=
        iSup₂_le fun j' hj' => le_iSup₂ (f := fun (j : Fin m) (_ : (j : ℕ) < i) => Ws j) j'
          (lt_of_lt_of_le (Fin.lt_def.mp (Set.mem_Iio.mp hj')) (Nat.lt_succ_iff.mp hj))
      have h1 := Submodule.map_mono (f := (e : W →ₗ[k] V)) hsub (hρ j g v hv)
      simpa [LinearEquiv.conj_apply] using h1
    have h2 := hle hx
    simpa using h2

end GlobalTheory.SemisimplificationCharpoly
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

theorem _root_.GlobalTheory.T.localUpperUnipotent_adelic_upperUnipotent : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin a) (w.adicCompletion E)), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) → (∀ i j : Fin a, j < i → (finGL E a (locGL E a w u)).val i j = 0) ∧ (∀ j : Fin a, (finGL E a (locGL E a w u)).val j j = 1) ∧ ∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (finGL E a (locGL E a w u)).val p.1 p.2 = sFin E (sLoc E w (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2)) := by
  first | exact @GlobalTheory.CuspRep.locTri_adelic | exact GlobalTheory.CuspRep.locTri_adelic | (intros; apply GlobalTheory.CuspRep.locTri_adelic <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.conjugates_separable_matrix_compact_mod_centralizer : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ (A₀ : Matrix (Fin r) (Fin r) F), A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) F), IsCompact Z → ∃ C : Set (GL (Fin r) F), IsCompact C ∧ ∀ g : GL (Fin r) F, (g : Matrix (Fin r) (Fin r) F) * A₀ * ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ Z → ∃ c ∈ C, ∃ t : GL (Fin r) F, (t : Matrix (Fin r) (Fin r) F) * A₀ = A₀ * (t : Matrix (Fin r) (Fin r) F) ∧ g = c * t) ∧ ∀ (A₀ : Matrix (Fin r) (Fin r) E), A₀.IsHermitian → A₀.charpoly.Separable → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ C : Set (Matrix.unitaryGroup (Fin r) E), IsCompact C ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * A₀ * star g.1 ∈ Z → ∃ c ∈ C, ∃ t : Matrix.unitaryGroup (Fin r) E, t.1 * A₀ = A₀ * t.1 ∧ g = c * t := by
  first | exact @GlobalTheory.OrbCpt.orbit_cpt | exact GlobalTheory.OrbCpt.orbit_cpt | (intros; apply GlobalTheory.OrbCpt.orbit_cpt <;> assumption)
end
