module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.SupIndep
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

namespace GlobalTheory

theorem tate_weight_graded : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ),
    (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) →
    ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)),
    (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) →
    ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  intro C σ Γ _ _ _ χ hT w J hJ
  classical
  suffices H : ∀ n, ∀ φ ∈ J, φ.support.card = n → ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J by
    intro φ hφ d; exact H _ φ hφ rfl d
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφ hn
  have IH : ∀ φ' ∈ J, φ'.support.card < n → ∀ d : ℤ, φ'.filter (fun m => w m = d) ∈ J :=
    fun φ' h1 h2 d => ih _ h2 φ' h1 rfl d
  by_cases h0 : φ = 0
  · subst h0; intro d; rw [Finsupp.filter_zero]; exact J.zero_mem
  obtain ⟨m0, hm0⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hc : φ m0 ≠ 0 := Finsupp.mem_support_iff.mp hm0
  set c := φ m0 with hcdef
  set φ0 : σ →₀ C := c⁻¹ • φ with hφ0def
  have hφ0 : φ0 ∈ J := J.smul_mem _ hφ
  have hsupp0 : φ0.support = φ.support := Finsupp.support_smul_eq (inv_ne_zero hc)
  have h1 : φ0 m0 = 1 := by
    simp only [φ0, Finsupp.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hc
  have hφeq : φ = c • φ0 := by
    simp only [φ0, smul_smul, mul_inv_cancel₀ hc, one_smul]
  suffices H0 : ∀ d : ℤ, φ0.filter (fun m => w m = d) ∈ J by
    intro d; rw [hφeq, Finsupp.filter_smul]; exact J.smul_mem _ (H0 d)
  have hcard : φ0.support.card = n := by rw [hsupp0, hn]
  have hm0' : m0 ∈ φ0.support := by rw [Finsupp.mem_support_iff, h1]; exact one_ne_zero
  have hψ : ∀ g : Γ, ∃ ψ ∈ J, ∀ m, ψ m =
      ((χ g ^ (-w m0) : Cˣ) : C) * (((χ g ^ w m : Cˣ) : C) * (g • φ0 m)) - φ0 m := by
    intro g
    obtain ⟨ψ', hψ'J, hψ'⟩ := hJ g φ0 hφ0
    refine ⟨((χ g ^ (-w m0) : Cˣ) : C) • ψ' - φ0, J.sub_mem (J.smul_mem _ hψ'J) hφ0, fun m => ?_⟩
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hψ']
  choose ψ hψJ hψm using hψ
  have hψm0 : ∀ g, ψ g m0 = 0 := by
    intro g
    rw [hψm, h1, smul_one, mul_one, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, sub_self]
  have hψ0 : ∀ g m, φ0 m = 0 → ψ g m = 0 := by
    intro g m h; rw [hψm, h, smul_zero, mul_zero, mul_zero, sub_zero]
  have hψsupp : ∀ g, (ψ g).support ⊆ φ0.support.erase m0 := by
    intro g m hm
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff] at hm
    refine ⟨?_, fun h => hm (hψ0 g m h)⟩
    rintro rfl; exact hm (hψm0 g)
  have hlt : ∀ g, (ψ g).support.card < n := fun g =>
    lt_of_le_of_lt (Finset.card_le_card (hψsupp g)) (hcard ▸ Finset.card_erase_lt_of_mem hm0')
  by_cases hall : ∀ g, ψ g = 0
  · have hw : ∀ m, φ0 m ≠ 0 → w m = w m0 := by
      intro m hm
      by_contra hne
      apply hm
      refine hT (w m0 - w m) (sub_ne_zero.mpr (Ne.symm hne)) (φ0 m) (fun g => ?_)
      have e := hψm g m
      rw [hall g, Finsupp.zero_apply, eq_comm, sub_eq_zero] at e
      have hex : w m0 - w m + -w m0 + w m = 0 := by ring
      conv_rhs => rw [← e]
      rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add,
        hex, zpow_zero, Units.val_one, one_mul]
    intro d
    by_cases hd : w m0 = d
    · rw [(Finsupp.filter_eq_self_iff _ _).mpr (fun m hm => (hw m hm).trans hd)]; exact hφ0
    · rw [(Finsupp.filter_eq_zero_iff _ _).mpr (fun m hm => by
        by_contra h; exact hd ((hw m h).symm.trans hm))]
      exact J.zero_mem
  · push_neg at hall
    obtain ⟨g, hg⟩ := hall
    obtain ⟨m1, hm1⟩ := Finsupp.support_nonempty_iff.mpr hg
    have hm1' := Finset.mem_of_mem_erase (hψsupp g hm1)
    have hψm1 : ψ g m1 ≠ 0 := Finsupp.mem_support_iff.mp hm1
    set a := φ0 m1 / ψ g m1 with hadef
    set φ' : σ →₀ C := φ0 - a • ψ g with hφ'def
    have hφ'J : φ' ∈ J := J.sub_mem hφ0 (J.smul_mem _ (hψJ g))
    have hφ'supp : φ'.support ⊆ φ0.support.erase m1 := by
      intro m hm
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff] at hm
      refine ⟨?_, fun h => hm ?_⟩
      · rintro rfl; apply hm
        simp only [φ', a, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          div_mul_cancel₀ _ hψm1, sub_self]
      · simp only [φ', Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h, hψ0 g m h,
          mul_zero, sub_zero]
    have hlt' : φ'.support.card < n :=
      lt_of_le_of_lt (Finset.card_le_card hφ'supp) (hcard ▸ Finset.card_erase_lt_of_mem hm1')
    intro d
    have hdec : φ0 = φ' + a • ψ g := by simp only [φ', sub_add_cancel]
    rw [hdec, Finsupp.filter_add, Finsupp.filter_smul]
    exact J.add_mem (IH _ hφ'J hlt' d) (J.smul_mem _ (IH _ (hψJ g) (hlt g) d))

end GlobalTheory
end

section

namespace GlobalTheory

theorem disjoint_finset_sup_of_supIndep_sup :
    ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V),
      F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) →
        Disjoint (F.sup G) (F.sup B) := by
  intro R V ι _ _ _ F G B hind hdis
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hs : s.SupIndep (fun i => G i ⊔ B i) := hind.subset (Finset.subset_insert _ _)
    have ih' := ih hs (fun i hi => hdis i (Finset.mem_insert_of_mem hi))
    have hA : Disjoint (G a ⊔ B a) (s.sup fun i => G i ⊔ B i) :=
      hind (Finset.subset_insert a s) (Finset.mem_insert_self a s) ha
    have hGs : s.sup G ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_left)
    have hBs : s.sup B ≤ s.sup (fun i => G i ⊔ B i) := Finset.sup_mono_fun (fun i _ => le_sup_right)
    rw [Finset.sup_insert, Finset.sup_insert, Submodule.disjoint_def]
    intro x hxG hxB
    obtain ⟨g, hg, g', hg', rfl⟩ := Submodule.mem_sup.mp hxG
    obtain ⟨b, hb, b', hb', hbb⟩ := Submodule.mem_sup.mp hxB
    have h1 : g - b ∈ G a ⊔ B a := Submodule.sub_mem _ (Submodule.mem_sup_left hg) (Submodule.mem_sup_right hb)
    have h2 : g - b ∈ s.sup (fun i => G i ⊔ B i) := by
      have : g - b = b' - g' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm b' b, hbb]
      rw [this]
      exact Submodule.sub_mem _ (hBs hb') (hGs hg')
    have h3 : g - b = 0 := (Submodule.disjoint_def.mp hA) _ h1 h2
    have hgb : g = b := sub_eq_zero.mp h3
    have hg0 : g = 0 := (Submodule.disjoint_def.mp (hdis a (Finset.mem_insert_self a s))) g hg (hgb ▸ hb)
    have hg'b' : g' = b' := by
      subst hgb
      exact add_left_cancel hbb.symm
    have hg'0 : g' = 0 := (Submodule.disjoint_def.mp ih') g' hg' (hg'b' ▸ hb')
    rw [hg0, hg'0, add_zero]

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.ShapeNeg

variable {O : Type} [CommRing O] (M : Type) [AddCommGroup M] [Module O M]

def Lev (c : O) : Type := ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M))

variable {M}

instance (c : O) : AddCommGroup (Lev M c) := inferInstanceAs (AddCommGroup ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : Module O (Lev M c) := inferInstanceAs (Module O ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : TopologicalSpace (Lev M c) := ⊥
instance (c : O) : DiscreteTopology (Lev M c) := ⟨rfl⟩
instance (c : O) : IsTopologicalAddGroup (Lev M c) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def Lev.val {c : O} (x : Lev M c) : M :=
  Subtype.val (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x

theorem Lev.smul_val {c : O} (x : Lev M c) : c • x.val = 0 := by
  have hx := LinearMap.mem_ker.1
    (Subtype.property (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x)
  exact hx

@[ext] theorem Lev.ext {c : O} {x y : Lev M c} (h : x.val = y.val) : x = y := by
  exact Subtype.ext (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) h

theorem Lev.val_add {c : O} (x y : Lev M c) : (x + y).val = x.val + y.val := rfl
theorem Lev.val_smul {c : O} (a : O) (x : Lev M c) : (a • x).val = a • x.val := rfl
theorem Lev.val_zero {c : O} : (0 : Lev M c).val = 0 := rfl

def Lev.mk {c : O} (m : M) (h : c • m = 0) : Lev M c :=
  (⟨m, by simpa using h⟩ : ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))

theorem Lev.val_mk {c : O} (m : M) (h : c • m = 0) : (Lev.mk m h).val = m := rfl

variable {G : Type} [Group G]

def levRep (ρ : Representation O G M) (c : O) : Representation O G (Lev M c) where
  toFun g :=
    { toFun := fun x => Lev.mk (ρ g x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
      map_add' := fun x y => Lev.ext (by
        simpa only [Lev.val_mk, Lev.val_add] using map_add (ρ g) x.val y.val)
      map_smul' := fun a x => Lev.ext (by
        simpa only [Lev.val_mk, Lev.val_smul] using map_smulₛₗ (ρ g) a x.val) }
  map_one' := LinearMap.ext fun x => Lev.ext
    (congrArg (fun f : Module.End O M => f x.val) (map_one ρ))
  map_mul' g h := LinearMap.ext fun x => Lev.ext
    (congrArg (fun f : Module.End O M => f x.val) (map_mul ρ g h))

theorem levRep_val (ρ : Representation O G M) (c : O) (g : G) (x : Lev M c) :
    (levRep ρ c g x).val = ρ g x.val := rfl

abbrev levZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    Module (ZMod (p ^ r)) (Lev M c) :=
  AddCommGroup.zmodModule (fun x => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
    apply Lev.ext
    show ((p ^ r : ℕ) • x.val) = 0
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← ha, mul_smul, Lev.smul_val, smul_zero])

def levRepZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) :
    @Representation (ZMod (p ^ r)) G (Lev M c) _ _ _ (levZ p r h) :=
  letI := levZ (M := M) p r h
  { toFun := fun g => (levRep ρ c g).toAddMonoidHom.toZModLinearMap (p ^ r)
    map_one' := LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_one (levRep ρ c))
    map_mul' := fun g g' => LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_mul (levRep ρ c) g g') }

theorem levRepZ_apply (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) (g : G) (x : Lev M c) :
    levRepZ p r h ρ g x = levRep ρ c g x := rfl

end GlobalTheory.ShapeNeg
end
end

section

namespace GlobalTheory

open MonoidAlgebra

theorem groupAlgebra_coeff_mul_fintype {R G : Type} [CommRing R] [Group G] [Fintype G]
    (x y : MonoidAlgebra R G) (a : G) :
    (x * y).coeff a = ∑ c : G, x.coeff (a * c⁻¹) * y.coeff c := by
  classical
  have hs : ∀ (f : G →₀ R) (g : G → R → R), (∀ i, g i 0 = 0) → f.sum g = ∑ i, g i (f i) :=
    fun f g h => Finsupp.sum_fintype f g h
  rw [MonoidAlgebra.coeff_mul, hs _ _ (fun i => by simp)]
  rw [Finset.sum_congr rfl fun b _ => hs _ _ (fun i => by simp)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : ∀ m : G, (m * c = a) ↔ (m = a * c⁻¹) := fun m => eq_mul_inv_iff_mul_eq.symm
  simp_rw [this]
  simp

theorem groupAlgebra_exists_right_inv_of_map {E L G : Type} [Field E] [Field L] [Group G]
    [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G) :
    (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) →
      ∃ v : MonoidAlgebra E G, x * v = 1 := by
  classical
  rintro ⟨vL, hvL⟩
  let M : Matrix G G E := fun a c => x.coeff (a * c⁻¹)

  have hsurj : Function.Surjective (M.map j).mulVec := by
    intro w
    let y : MonoidAlgebra L G := ofCoeff (Finsupp.equivFunOnFinite.symm w)
    refine ⟨fun c => (vL * y).coeff c, ?_⟩
    funext a
    have h1 : (MonoidAlgebra.mapRingHom G j x * (vL * y)).coeff a = w a := by
      rw [← mul_assoc, hvL, one_mul]
      rfl
    rw [groupAlgebra_coeff_mul_fintype] at h1
    simp only [MonoidAlgebra.coeff_mapRingHom] at h1
    exact h1
  have hU : IsUnit (M.map j) := Matrix.mulVec_surjective_iff_isUnit.1 hsurj
  have hdetL : IsUnit (j M.det) := by
    rw [RingHom.map_det]
    exact (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet : M.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hdetL
    exact not_isUnit_zero hdetL
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (isUnit_iff_ne_zero.2 hdet)
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hM
    (fun a => (1 : MonoidAlgebra E G).coeff a)
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm u), ?_⟩
  apply MonoidAlgebra.ext
  ext a
  rw [groupAlgebra_coeff_mul_fintype]
  have := congrFun hu a
  simpa [Matrix.mulVec, dotProduct, M] using this

end GlobalTheory
end

section

namespace GlobalTheory.OrdMul

open MvPolynomial

theorem coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  classical

  have key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N →
      (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hμ hm hK
      set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'
      have hdeg' : m'.degree < N + 1 := by
        rw [hm', map_add (f := _), Finsupp.degree_single]; omega
      have hK' : ∀ j ∈ K, m' j = 0 := by
        intro j hj
        have hqj : q ≠ j := fun h => hq (h ▸ hj)
        simp [hm', hK j hj, Finsupp.single_apply, hqj]
      have hH := H m' hdeg' hK'
      rw [MvPolynomial.coeff_mul] at hH
      have hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m' := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal, hm']; exact add_comm _ _
      rw [← Finset.add_sum_erase _ _ hmem] at hH
      have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m),
          a.coeff x.1 * F.coeff x.2 ∈ I := by
        refine Ideal.sum_mem _ (fun x hx => ?_)
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases hi : x.1 = 0
        · rw [hi, h0, zero_mul]; exact I.zero_mem
        · apply I.mul_mem_left
          have hiq : x.1 ≠ Finsupp.single q 1 := by
            intro h
            apply hne
            refine Prod.ext h ?_
            rw [h, hm', add_comm m] at hx
            exact add_left_cancel hx
          have hxq : x.1 q + x.2 q = m q + 1 := by
            have := congrArg (fun f : ι →₀ ℕ => f q) hx
            simpa [hm'] using this
          have hxe : x.1.erase q + x.2.erase q = m.erase q := by
            have := congrArg (Finsupp.erase q) hx
            simpa [hm', Finsupp.erase_add] using this
          have hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree := by
            rw [← map_add (f := _), hxe]
          have hdx : x.1.degree + x.2.degree = m.degree + 1 := by
            have := congrArg Finsupp.degree hx
            simpa [hm'] using this
          have hd1 : x.1.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)

          have hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree := by
            by_cases he : x.1.erase q = 0
            · have hs : Finsupp.single q (x.1 q) = x.1 := by
                simpa [he] using Finsupp.single_add_erase q x.1
              have h0' : x.1 q ≠ 0 := by
                intro h; apply hi; rw [← hs, h, Finsupp.single_zero]
              have h1' : x.1 q ≠ 1 := by
                intro h; apply hiq; rw [← hs, h]
              omega
            · have : (x.1.erase q).degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)
              omega
          refine ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_
          intro j hj
          have h1 := hK' j hj
          rw [← hx] at h1
          simp only [Finsupp.add_apply] at h1
          omega
      have hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I :=
        (Ideal.add_mem_iff_left I hrest).mp hH
      exact (Ideal.unit_mul_mem_iff_mem I hu).mp hmain
  exact fun m hm hK => key _ m rfl hm hK

theorem coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this

end GlobalTheory.OrdMul
end

section

noncomputable section

namespace GlobalTheory.LogU

def truncLogF {R : Type} [CommRing R] (n : ℕ) (u : R) : R :=
  ∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * u ^ (k + 1)

theorem map_truncLogF {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (n : ℕ) (u : R) :
    f (truncLogF n u) = truncLogF n (f u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [truncLogF, map_sum, map_mul, map_pow, map_neg, map_one, map_natCast]

def logDefect (n : ℕ) : MvPolynomial (Fin 2) ℤ :=
  truncLogF n (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 1) -
    truncLogF n (MvPolynomial.X 0) - truncLogF n (MvPolynomial.X 1)

theorem aeval_logDefect {R : Type} [CommRing R] (n : ℕ) (a b : R) :
    MvPolynomial.aeval ![a, b] (logDefect n) = truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b := by
  have h := fun u => map_truncLogF (MvPolynomial.aeval (R := ℤ) ![a, b]).toRingHom n u
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  simp [logDefect, h]

end GlobalTheory.LogU
end
end
