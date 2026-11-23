module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HodgeCoh

set_option autoImplicit false

namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X : Scheme.{0}}

theorem formPull_id (s : X ⟶ Sp k) (j : ℕ) (U : X.Opens) (x : OmU s U j) :
    formPull (f := 𝟙 X) (Category.id_comp s) U j x = x :=
  SemiHom.mOm_id _ (fun _ ↦ rfl) x

theorem omegaPull_id (s : X ⟶ Sp k) (j : ℕ) :
    omegaPull (f := 𝟙 X) (Category.id_comp s) j =
      (Scheme.Modules.pushforwardId X).inv.app (Omega s j) := by
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit _ _ _ _).symm
  ext U x
  exact congrArg ((toOmega s j).app U).hom (formPull_id s j U.unop x)

theorem hodgePull_id (s : X ⟶ Sp k) (j q : ℕ) (x : hodgeH s j q) :
    hodgePull (f := 𝟙 X) (Category.id_comp s) j q x = x := by
  letI := algΓ s
  apply (cohOn.toH' (Omega s j) ⊤ q).injective
  refine (cohOn.toH'_pull (appTop_algebraMap (Category.id_comp s))
    (omegaPull (Category.id_comp s) j) (le_refl ((𝟙 X) ⁻¹ᵁ ⊤)) (n := q) x).trans ?_
  rw [omegaPull_id]
  exact (SheafPull.pull_id (X := X.toTopCat) (𝟙 ((toAbSheaf X).obj (Omega s j))) q
    (homOfLE (le_refl ⊤)) _).trans (by rw [SheafLES.map_id]; exact SheafLES.res_id _ _ _)

end GlobalTheory.HodgeCoh
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimpleDecomp

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem isInv_inf {ρ : Γ →* GL (Fin a) k} {U V : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) :=
  fun g v hv => ⟨hU g v hv.1, hV g v hv.2⟩

theorem isInv_top (ρ : Γ →* GL (Fin a) k) : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

theorem exists_irr_le {ρ : Γ →* GL (Fin a) k} {U : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (h0 : U ≠ ⊥) : ∃ W, W ≤ U ∧ IsIrrSub ρ W := by
  obtain ⟨W, ⟨hW0, hWi, hWU⟩, hmin⟩ := (wellFounded_lt (α := Submodule k (Fin a → k))).has_min
    {W | W ≠ ⊥ ∧ IsInv ρ W ∧ W ≤ U} ⟨U, h0, hU, le_rfl⟩
  refine ⟨W, hWU, hW0, hWi, fun W' hle hi => ?_⟩
  by_cases h : W' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin W' ⟨h, hi, hle.trans hWU⟩ (lt_of_le_of_ne hle hne)

theorem disjoint_sup_of_le {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] {x b c w : α}
    (hx : x ≤ c) (hb : b ≤ c) (hxb : Disjoint x b) (hw : Disjoint w c) : Disjoint x (w ⊔ b) := by
  have hc : (b ⊔ w) ⊓ c = b := by
    rw [sup_inf_assoc_of_le w hb, hw.eq_bot, sup_bot_eq]
  rw [disjoint_iff_inf_le]
  calc x ⊓ (w ⊔ b) ≤ x ⊓ b := by
        refine le_inf inf_le_left ?_
        exact (le_inf (inf_le_right.trans (sup_comm w b).le) (inf_le_left.trans hx)).trans hc.le
    _ ≤ ⊥ := hxb.le_bot

theorem exists_decomp {ρ : Γ →* GL (Fin a) k} (hρ : IsSSRep ρ) (U : Submodule k (Fin a → k))
    (hU : IsInv ρ U) : ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      iSupIndep Vs ∧ iSup Vs = U ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  induction U using WellFoundedLT.induction with
  | _ U ih =>
  by_cases h0 : U = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp [h0], fun j => j.elim0⟩
  obtain ⟨W, hWU, hW⟩ := exists_irr_le hU h0
  obtain ⟨W', hW'i, hc⟩ := hρ W hW.2.1
  have hlt : U ⊓ W' < U := by
    refine lt_of_le_of_ne inf_le_left fun heq => hW.1 ?_
    have hle : W ≤ W' := hWU.trans (heq.symm ▸ inf_le_right)
    exact hc.disjoint.eq_bot_of_le hle
  obtain ⟨n, Vs, hind, hsup, hirr⟩ := ih _ hlt (isInv_inf hU hW'i)
  have hVs : ∀ j, Vs j ≤ U ⊓ W' := fun j => hsup ▸ le_iSup Vs j
  refine ⟨n + 1, Fin.cons W Vs, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · refine hc.disjoint.mono_right (iSup₂_le fun j hj => ?_)
      refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hj
      simpa using (hVs j).trans inf_le_right
    · have hle : (⨆ (j) (_ : j ≠ Fin.succ i), (Fin.cons W Vs : Fin (n + 1) → _) j) ≤
          W ⊔ ⨆ (j) (_ : j ≠ i), Vs j := by
        refine iSup₂_le fun j hj => ?_
        refine Fin.cases (fun _ => ?_) (fun j hj => ?_) j hj
        · simp
        · have hji : j ≠ i := fun h => hj (h ▸ rfl)
          simp only [Fin.cons_succ]
          exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hji)
      simp only [Fin.cons_succ]
      refine (disjoint_sup_of_le (hVs i) (iSup₂_le fun j _ => hVs j) (hind i)
        (hc.disjoint.mono_right inf_le_right)).mono_right hle
  · have hS : iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) = W ⊔ iSup Vs := by
      refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ (iSup_le fun j => ?_))
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simpa using le_sup_of_le_right (le_iSup Vs j)
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) 0
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) j.succ
    rw [hS, hsup, inf_comm, ← sup_inf_assoc_of_le W' hWU, hc.sup_eq_top, top_inf_eq]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hW
    · simpa using hirr j

end GlobalTheory.SemisimpleDecomp

theorem GlobalTheory.semisimple_matrix_rep_decomp : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  intro k Γ _ _ a ρ hρ
  obtain ⟨n, Vs, hind, hsup, hirr⟩ :=
    GlobalTheory.SemisimpleDecomp.exists_decomp hρ ⊤ (GlobalTheory.SemisimpleDecomp.isInv_top ρ)
  exact ⟨n, Vs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).2 ⟨hind, hsup⟩,
    hirr⟩
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

noncomputable section
namespace GlobalTheory.LocPlace

theorem norm_le_one_of_isIntegral' {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_int_le_one (l : ℕ) [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : ‖c (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (map_isIntegral_int c x.isIntegral_coe)

theorem norm_natCast_prime_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : PadicAlgCl l)‖ < 1 := by
  have h : ((l : ℕ) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

def ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : Ideal (𝓞 E) where
  carrier := {x | ‖c (x : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have e : ((a + b : 𝓞 E) : E) = (a : E) + (b : E) := by simp
    rw [e, map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  smul_mem' := by
    intro a b hb
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    push_cast
    rw [map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le_one l c a)) hb

theorem mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) (x : 𝓞 E) : x ∈ ballIdeal l E c ↔ ‖c (x : E)‖ < 1 := Iff.rfl

theorem ballIdeal_isPrime (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : (ballIdeal l E c).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : (1 : 𝓞 E) ∈ ballIdeal l E c := h ▸ Submodule.mem_top
    rw [mem_ballIdeal] at h1
    simp at h1
  · intro a b hab
    rw [mem_ballIdeal, mem_ballIdeal] at *
    push_cast at hab
    rw [map_mul, norm_mul] at hab
    by_contra hcon
    push_neg at hcon
    have ha := le_antisymm (norm_int_le_one l c a) hcon.1
    have hb := le_antisymm (norm_int_le_one l c b) hcon.2
    rw [ha, hb] at hab
    norm_num at hab

theorem natCast_mem_ballIdeal (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ((l : ℕ) : 𝓞 E) ∈ ballIdeal l E c := by
  rw [mem_ballIdeal]
  push_cast
  rw [map_natCast]
  exact norm_natCast_prime_lt_one l

theorem ballIdeal_ne_bot (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l) : ballIdeal l E c ≠ ⊥ := by
  intro h
  have h1 := natCast_mem_ballIdeal l E c
  rw [h, Ideal.mem_bot] at h1
  have h2 : ((l : ℕ) : E) = 0 := by exact_mod_cast congrArg (fun y : 𝓞 E => (y : E)) h1
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)

theorem exists_place_of_emb : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E]
    (c : E →+* PadicAlgCl l), ∃ v : HeightOneSpectrum (𝓞 E), v ∈ placesOver E l ∧
      ∀ x : 𝓞 E, x ∈ v.asIdeal ↔ ‖c (x : E)‖ < 1 := by
  intro l _ E _ _ c
  refine ⟨⟨ballIdeal l E c, ballIdeal_isPrime l E c, ballIdeal_ne_bot l E c⟩, ?_, fun x => Iff.rfl⟩
  exact natCast_mem_ballIdeal l E c

end GlobalTheory.LocPlace
end
end

section

namespace GlobalTheory.AbsolutelyIrreduciblePullback

open Formalism.MainNotions.N

def pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) : Submodule K (Fin n → K) where
  carrier := {v | f ∘ v ∈ W}
  add_mem' := by
    intro a b ha hb
    have : f ∘ (a + b) = f ∘ a + f ∘ b := by
      funext i; simp
    show f ∘ (a + b) ∈ W
    rw [this]
    exact W.add_mem ha hb
  zero_mem' := by
    have : f ∘ (0 : Fin n → K) = 0 := by
      funext i; simp
    show f ∘ (0 : Fin n → K) ∈ W
    rw [this]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have : f ∘ (c • v) = f c • (f ∘ v) := by
      funext i; simp
    show f ∘ (c • v) ∈ W
    rw [this]
    exact W.smul_mem _ hv

theorem mem_pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) (v : Fin n → K) : v ∈ pullSub f W ↔ f ∘ v ∈ W := by
  exact Iff.rfl

theorem exists_comp_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (hf : Function.Surjective f)
    {n : ℕ} (w : Fin n → L) : ∃ v : Fin n → K, f ∘ v = w := by
  choose v hv using fun i => hf (w i)
  exact ⟨v, funext hv⟩

theorem isInv_pullSub {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (W : Submodule L (Fin n → L)) (hW : IsInv (mapRep f ρ) W) :
    IsInv ρ (pullSub f W) := by
  intro g v hv
  rw [mem_pullSub] at hv ⊢
  have heq : f ∘ ((ρ g : Matrix (Fin n) (Fin n) K).mulVec v) =
      ((mapRep f ρ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec (f ∘ v) := by
    funext i
    exact RingHom.map_mulVec f _ v i
  rw [heq]
  exact hW g (f ∘ v) hv

theorem absIrrSub_top {Γ : Type} [Group Γ] {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  have hsurj : Function.Surjective (algebraMap K (AlgebraicClosure K)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := AlgebraicClosure K)).2
  have hspan : Submodule.span (AlgebraicClosure K)
      ((fun v => (algebraMap K (AlgebraicClosure K)) ∘ v) '' ((⊤ : Submodule K (Fin n → K)) : Set (Fin n → K))) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
    exact Submodule.subset_span ⟨v, Submodule.mem_top, rfl⟩
  unfold AbsIrrSub IsIrrSub
  rw [hspan]
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact top_ne_bot
  · intro W' _ hW'
    rcases h _ (isInv_pullSub (algebraMap K (AlgebraicClosure K)) ρ W' hW') with h0 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := (mem_pullSub _ _ _).mpr hw
      rw [h0, Submodule.mem_bot] at hv
      subst hv
      rw [Submodule.mem_bot]
      funext i
      simp
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := by
        rw [h1]
        trivial
      exact (mem_pullSub _ _ _).mp hv

end GlobalTheory.AbsolutelyIrreduciblePullback
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem isoSub_span_map : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)), IsInv ρ W₁ → IsInv ρ W₂ → IsoSub ρ W₁ W₂ → IsoSub (mapRep f ρ) (Submodule.span L ((fun v => f ∘ v) '' (W₁ : Set (Fin a → k)))) (Submodule.span L ((fun v => f ∘ v) '' (W₂ : Set (Fin a → k)))) := by
  intro k Γ _ _ L _ f a ρ W₁ W₂ h₁ h₂ ⟨e, he⟩
  obtain ⟨g₁, hg₁⟩ := LinearMap.exists_extend (W₂.subtype ∘ₗ (e : W₁ →ₗ[k] W₂))
  obtain ⟨g₂, hg₂⟩ := LinearMap.exists_extend (W₁.subtype ∘ₗ (e.symm : W₂ →ₗ[k] W₁))
  have hg₁' : ∀ v : W₁, g₁ v = (e v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₁ v
  have hg₂' : ∀ v : W₂, g₂ v = (e.symm v : Fin a → k) := fun v => by
    simpa using LinearMap.congr_fun hg₂ v
  have key : ∀ (M : Matrix (Fin a) (Fin a) k) (v : Fin a → k),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v; funext i; exact (RingHom.map_mulVec f M v i).symm
  let φ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₁).map f).mulVecLin
  let ψ : (Fin a → L) →ₗ[L] (Fin a → L) := ((LinearMap.toMatrix' g₂).map f).mulVecLin
  have hφ : ∀ w (hw : w ∈ W₁), φ (f ∘ w) = f ∘ (e ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₁).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₁' ⟨w, hw⟩)
  have hψ : ∀ w (hw : w ∈ W₂), ψ (f ∘ w) = f ∘ (e.symm ⟨w, hw⟩ : Fin a → k) := by
    intro w hw
    show ((LinearMap.toMatrix' g₂).map f).mulVec (f ∘ w) = _
    rw [key, LinearMap.toMatrix'_mulVec]
    exact congrArg _ (hg₂' ⟨w, hw⟩)
  set S₁ := (fun v => f ∘ v) '' (W₁ : Set (Fin a → k)) with hS₁
  set S₂ := (fun v => f ∘ v) '' (W₂ : Set (Fin a → k)) with hS₂
  have mφ : ∀ x ∈ Submodule.span L S₁, φ x ∈ Submodule.span L S₂ := by
    intro x hx
    have : Submodule.span L S₁ ≤ (Submodule.span L S₂).comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change φ (f ∘ w) ∈ Submodule.span L S₂
      rw [hφ w hw]
      exact Submodule.subset_span ⟨_, (e ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have mψ : ∀ x ∈ Submodule.span L S₂, ψ x ∈ Submodule.span L S₁ := by
    intro x hx
    have : Submodule.span L S₂ ≤ (Submodule.span L S₁).comap ψ := by
      rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      change ψ (f ∘ w) ∈ Submodule.span L S₁
      rw [hψ w hw]
      exact Submodule.subset_span ⟨_, (e.symm ⟨w, hw⟩).2, rfl⟩
    exact this hx
  have ψφ : ∀ x ∈ Submodule.span L S₁, ψ (φ x) = x := by
    intro x hx
    have : Set.EqOn (ψ ∘ₗ φ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₁ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hφ w hw, hψ _ (e ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  have φψ : ∀ x ∈ Submodule.span L S₂, φ (ψ x) = x := by
    intro x hx
    have : Set.EqOn (φ ∘ₗ ψ) (LinearMap.id : (Fin a → L) →ₗ[L] (Fin a → L)) S₂ := by
      rintro _ ⟨w, hw, rfl⟩
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hψ w hw, hφ _ (e.symm ⟨w, hw⟩).2]
      simp
    exact LinearMap.eqOn_span' this hx
  let φ' : Submodule.span L S₁ →ₗ[L] Submodule.span L S₂ := φ.restrict mφ
  let ψ' : Submodule.span L S₂ →ₗ[L] Submodule.span L S₁ := ψ.restrict mψ
  refine ⟨LinearEquiv.ofLinear φ' ψ'
    (LinearMap.ext fun x => Subtype.ext (φψ x x.2))
    (LinearMap.ext fun x => Subtype.ext (ψφ x x.2)), ?_⟩
  intro g v hv
  show φ (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec v)
      = ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVec (φ v)
  have : Set.EqOn (φ ∘ₗ ((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin)
      (((ρ g : Matrix (Fin a) (Fin a) k).map f).mulVecLin ∘ₗ φ) S₁ := by
    rintro _ ⟨w, hw, rfl⟩
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply]
    have hgw : (ρ g : Matrix (Fin a) (Fin a) k).mulVec w ∈ W₁ := h₁ g w hw
    rw [key, hφ _ hgw, hφ w hw, key]
    congr 1
    exact he g ⟨w, hw⟩ hgw
  exact LinearMap.eqOn_span' this v.2

end GlobalTheory
end
