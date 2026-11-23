module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle023
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle019
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle005
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle013
public import Development.WeilBound.CoreStatements.HodgeTatePoints.FormMemLin
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle015
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RaSmith
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Gd

section Pt

variable {C : Type} [Field C] {O : Type} [CommRing O] [Algebra O C]
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {κ : O} {N : ℕ}
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem e_swap (x y : V) : P.e x y = -P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

theorem torusExtensionPair_correction_eq_value_quotient {σ : E →+* C} (hσ : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) {u : V}
    (hu : u ∈ eigSp P.ρ σ) (π : O) (h : ∀ j, ∃ z : O, P.e u (P.t j) = algebraMap O C (π * z)) :
    ∀ y ∈ P.T, ∃ z : O, P.e u y = algebraMap O C (π * z) := by
  intro y hy
  rw [P.free.2.2] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨j, k⟩, rfl⟩ := hy
    obtain ⟨b, hb⟩ := (RingOfIntegers.mapRingEquiv c).surjective (RingOfIntegers.basis E k)
    obtain ⟨z, hz⟩ := h j
    obtain ⟨s, hs⟩ := hσ b
    refine ⟨s * z, ?_⟩
    simp only
    rw [← hb, ← P.adj, LatBasic.mem_eigSp.1 hu b, map_smul, LinearMap.smul_apply, hz, ← hs,
      smul_eq_mul, ← map_mul]
    congr 1
    ring
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), ha, hb, mul_add, map_add (f := _)]⟩
  | smul a x _ hx =>
    obtain ⟨b, hb⟩ := hx
    refine ⟨a * b, ?_⟩
    rw [← algebraMap_smul C a x, map_smul, hb, smul_eq_mul, ← map_mul]
    congr 1
    ring

end Pt

theorem pt_comp_zero : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω) (σ : E →+* C) (d π : O) (x : Fin N → O) (w : V), Submodule.span O {algebraMap O C d} = Submodule.span O {y : C | ∃ z ∈ differentIdeal ℤ (𝓞 E), y = σ (z : E)} → w ∈ P.W' σ → (∀ j, ∃ z : O, ∑ l, algebraMap O C (x l) * P.e (d • eigProj P.ρ σ (P.t l)) (P.t j) = P.e w (P.t j) + algebraMap O C (π * z)) → ∃ y ∈ P.omHT σ, ∑ l, x l • eigProj P.ρΩ σ (P.ht (P.t l)) = π • y := by
  intro C _ v O _ _ hv _ _ E _ _ c hc κ N V _ _ _ _ Ω _ _ _ _ P σ d π x w hd hw hx
  have hσ := (exists_diff_generator C v O hv E σ).1
  have hinj := hv.hom_inj
  obtain ⟨-, -, -, hcomm, -, hom, hdual, -⟩ := htPoint_basic C v O hv E c hc κ N V Ω P
  have hd0 := (different_generator_dualInt O C E σ d hinj hσ hd).1
  have hq := (SubDiffQuot.eigSub_eq_different_smul_eigQuot O C V E P.ρ P.T N P.t σ d hinj hσ hd
    P.free).1
  set s : V := ∑ l, x l • eigProj P.ρ σ (P.t l) with hs
  have hsE : s ∈ eigSp P.ρ σ := Submodule.sum_mem _ fun l _ => by
    rw [← algebraMap_smul C (x l)]
    exact Submodule.smul_mem _ _ (LatBasic.eigProj_mem _ _ _)
  set u : V := d • s - w with hu
  have huE : u ∈ eigSp P.ρ σ := by
    refine Submodule.sub_mem _ ?_ hw.2.2
    rw [← algebraMap_smul C d]
    exact Submodule.smul_mem _ _ hsE
  have hut : ∀ j, ∃ z : O, P.e u (P.t j) = algebraMap O C (π * z) := fun j => by
    obtain ⟨z, hz⟩ := hx j
    refine ⟨z, ?_⟩

    rw [hu, map_sub, LinearMap.sub_apply, sub_eq_iff_eq_add', ← hz, hs, Finset.smul_sum, map_sum,
    LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_comm d (x l), ← algebraMap_smul C (x l), map_smul, LinearMap.smul_apply, smul_eq_mul]
  have huT := torusExtensionPair_correction_eq_value_quotient P hσ huE π hut
  obtain ⟨u', hu'T, hu'E, hu'⟩ : ∃ u' ∈ P.T, u' ∈ eigSp P.ρ σ ∧ u = π • u' := by
    by_cases hπ : algebraMap O C π = 0
    · refine ⟨0, P.T.zero_mem, Submodule.zero_mem _, ?_⟩
      rw [smul_zero]
      refine P.nondeg u fun y => ?_
      rw [e_swap, neg_eq_zero]
      have hy : y ∈ Submodule.span C (P.T : Set V) := by rw [P.free.2.1]; trivial
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨z, hz⟩ := huT y hy
        rw [hz, map_mul, hπ, zero_mul]
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), ha, hb, add_zero]
      | smul a b _ hb => rw [map_smul, hb, smul_zero]
    · refine ⟨(algebraMap O C π)⁻¹ • u, ?_, Submodule.smul_mem _ _ huE, ?_⟩
      · rw [← hdual]
        intro y hy
        obtain ⟨z, hz⟩ := huT y hy
        refine ⟨z, ?_⟩
        rw [LinearMap.flip_apply, map_smul, LinearMap.smul_apply, hz, map_mul, smul_eq_mul,
          inv_mul_cancel_left₀ hπ]
      · rw [← algebraMap_smul C π, smul_smul, mul_inv_cancel₀ hπ, one_smul]
  have hy : (algebraMap O C d)⁻¹ • u' ∈ eigQuot P.ρ σ P.T := by
    rw [hq, ← algebraMap_smul C d, smul_smul, mul_inv_cancel₀ hd0, one_smul]
    exact ⟨hu'T, hu'E⟩
  refine ⟨P.ht ((algebraMap O C d)⁻¹ • u'), ?_, ?_⟩
  · rw [hom]
    exact ⟨_, hy, rfl⟩
  · have hw0 : P.ht w = 0 := hw.1
    have h1 : P.ht s = ∑ l, x l • eigProj P.ρΩ σ (P.ht (P.t l)) := by

      rw [hs, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [LinearMap.map_smul_of_tower, hcomm]
    have h2 : algebraMap O C d • P.ht s = algebraMap O C π • P.ht u' := by
      have := congrArg P.ht hu'
      rw [hu, map_sub, hw0, sub_zero, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower] at this
      rw [algebraMap_smul, algebraMap_smul, this]
    rw [← h1, map_smul, ← algebraMap_smul C π, smul_comm, ← h2, smul_smul, inv_mul_cancel₀ hd0,
      one_smul]

end PositivityTheory.HtPt.Gd
end
end

section

noncomputable section

namespace PositivityTheory.HtPt.Gi

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra
  PositivityTheory.HtPt.Twpdiv

def levMap {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) : LevGrp La p n →* LevGrp La p n :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ φ.toIntLinearMap (by
    rintro _ ⟨b, rfl⟩
    exact ⟨φ b, (map_nsmul φ _ b).symm⟩)).toAddMonoidHom

theorem levMap_lev {La : Type} [AddCommGroup La] (p n : ℕ) (φ : La →+ La) (a : La) :
    levMap p n φ (lev p n a) = lev p n (φ a) := rfl

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] {X : OrdTower p O La L} {G : PDivGroup p O}
  (e : ∀ n, G.A n ≃ₐ[O] X.A n) {τ : La →+ G.Tate}

def evG (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O := (evalAt (X.A n) t).comp (e n).toAlgHom

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : evG e n t g = (e n g).1 t := rfl

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem sepG (n : ℕ) : Sep (evG e n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))

variable {e}

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_lev (hre : X.Realises G e τ) (n : ℕ) (a : La) : evG e n (lev p n a) = (τ a).pt n :=
  AlgHom.ext fun g => (hre.pt a n g).symm

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_one (hre : X.Realises G e τ) (n : ℕ) (g : G.A n) : evG e n 1 g = counit (R := O) g := by
  rw [← lev_zero, evG_lev hre, map_zero]
  rfl

omit [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_mul (hre : X.Realises G e τ) (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
    pair (evG e n s) (evG e n t) (comul (R := O) g) = evG e n (s * t) g := by
  obtain ⟨a, rfl⟩ := lev_surjective p n s
  obtain ⟨b, rfl⟩ := lev_surjective p n t
  rw [← lev_add, evG_lev hre, evG_lev hre, evG_lev hre, map_add (f := _)]
  exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm

def pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) : G.A n →ₐ[O] G.A n :=
  Ord.liftTo (evG e n) (sepG e n) (fun t => evG e n (levMap p n φ t)) fun g =>
    ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), (h n (e n g).1 _ fun _ => rfl).1 (e n g).2⟩, fun t => by
      rw [evG_apply, AlgEquiv.apply_symm_apply]; rfl⟩

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) :
    (evG e n t).comp (pullA (e := e) h n) = evG e n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t

omit [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] in
theorem evG_pullA' {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
    evG e n t (pullA (e := e) h n g) = evG e n (levMap p n φ t) g := DFunLike.congr_fun (evG_pullA h n t) g

def pullB (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) (n : ℕ) :
    G.A n →ₐc[O] G.A n :=
  BialgHom.ofAlgHom (pullA (e := e) h n)
    (AlgHom.ext fun g => by
      change counit (R := O) (pullA (e := e) h n g) = counit (R := O) g
      rw [← evG_one hre, ← evG_one hre, evG_pullA', map_one])
    (AlgHom.ext fun g => (sepG e n).pair (sepG e n) _ _ fun z => by
      change pair _ _ (Algebra.TensorProduct.map _ _ (comul (R := O) g)) =
        pair _ _ (comul (R := O) (pullA (e := e) h n g))
      rw [pair_map, evG_pullA, evG_pullA, evG_mul hre, evG_mul hre, evG_pullA', map_mul])

def endG (hre : X.Realises G e τ) {φ : La →+ La} {dφ : L →ₗ[O] L} (h : X.Acts φ dφ) : G ⟶ G where
  app := pullB hre h
  comm n := BialgHom.ext fun g => sepG e n _ _ fun t => by
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    change (e n (G.res n (pullA (e := e) h (n + 1) g))).1 _ = evG e n _ (pullA (e := e) h n (G.res n g))
    rw [hre.res, evG_pullA', levMap_lev, evG_apply, hre.res, ← evG_apply, evG_pullA', levMap_lev, map_nsmul,
      evG_apply]

end PositivityTheory.HtPt.Gi

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Gi.tower_end : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  refine ⟨fun φ dφ h => ⟨PositivityTheory.HtPt.Gi.endG hre h, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_),
    fun n g a => PositivityTheory.HtPt.Gi.evG_pullA' h n _ g⟩, fun H f f' hf =>
      PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g =>
        PositivityTheory.HtPt.Gi.sepG e n _ _ fun t => ?_)⟩
  · rw [tateMap_pt, ← PositivityTheory.HtPt.Gi.evG_lev hre, ← PositivityTheory.HtPt.Gi.evG_lev hre]
    exact PositivityTheory.HtPt.Gi.evG_pullA' h n _ g
  · obtain ⟨a, rfl⟩ := PositivityTheory.HtPt.Twpdiv.lev_surjective p n t
    rw [PositivityTheory.HtPt.Gi.evG_lev hre, ← tateMap_pt, ← tateMap_pt, hf]
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Ge

section
variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

noncomputable def qL (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem qL_apply (σ : E →+* K) (x : Fin N → A) : qL D σ x = D.q σ x := rfl

theorem frame_expand {σ : E →+* K} {m j k : ℕ}
    {i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)}
    {bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))} {bM : Basis (Fin k) A (D.omHT σ)}
    {g : Matrix (Fin N) (Fin j ⊕ Fin k) A} (hex : D.ExactMod σ m i) (hg : D.IsFrame σ m i bW bM g)
    (x : Fin N → A) (t : Fin k → A) (y : Ω) (hy : y ∈ D.omHT σ)
    (e : D.q σ x = ∑ a, t a • (bM a : Ω) + ((p : A) ^ m) • y) :
    ∃ (s : Fin j → A) (z : Fin N → A), x = g.mulVec (Sum.elim s t) + ((p : A) ^ m) • z := by
  obtain ⟨hcol1, hcol2⟩ := hg
  choose x'' hx'' using hcol1
  choose yM hyM hq using hcol2
  have hx1 : ∃ y₁ ∈ D.omHT σ, D.q σ (x - ∑ a, t a • (fun l => g l (Sum.inr a))) = ((p : A) ^ m) • y₁ := by
    refine ⟨y - ∑ a, t a • yM a, ?_, ?_⟩
    · exact Submodule.sub_mem _ hy (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hyM a))
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [← qL_apply, map_sub, map_sum]
      simp only [map_smul, qL_apply, hq, e, smul_add, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
      simp only [smul_comm (t _) ((p : A) ^ m)]
      abel
  obtain ⟨w, x', hw⟩ := (hex.2.1 _).1 hx1
  refine ⟨bW.repr w, x' - ∑ b, bW.repr w b • x'' b, ?_⟩
  have hiw : i w = ∑ b, bW.repr w b • i (bW b) := by
    conv_lhs => rw [← bW.sum_repr w]

    rw [map_sum]
    simp only [map_smul]
  have hcolL : ∀ b, i (bW b) = (fun l => g l (Sum.inl b)) - ((p : A) ^ m) • x'' b := fun b => by
    rw [hx'' b]
    abel
  have hx : x = ∑ a, t a • (fun l => g l (Sum.inr a)) + i w + ((p : A) ^ m) • x' := by
    rw [add_assoc, ← hw]
    abel
  rw [hx, hiw]
  simp only [hcolL]
  ext l
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply,
    Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
  ring_nf
  have s1 : ∑ x, g l (Sum.inl x) * (bW.repr w) x = ∑ x, (bW.repr w) x * g l (Sum.inl x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s2 : ∑ x, g l (Sum.inr x) * t x = ∑ x, t x * g l (Sum.inr x) :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have s3 : ∑ x, (p : A) ^ m * (bW.repr w) x * x'' x l = ∑ x, (bW.repr w) x * (p : A) ^ m * x'' x l :=
    Finset.sum_congr rfl fun _ _ => by ring
  rw [s1, s2, s3]
  ring

end

theorem frame_exists : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (m j k : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)) (bW : Basis (Fin j) A (Module.Dual A (D.omHT (σ.comp c.toRingHom)))) (bM : Basis (Fin k) A (D.omHT σ)) (eqv : Fin j ⊕ Fin k ≃ Fin N), (∀ x, D.q σ x ∈ D.omHT σ) → D.ExactMod σ m i → (∃ g, D.IsFrame σ m i bW bM g) ∧ ∀ g, D.IsFrame σ m i bW bM g → ∃ h r : A, (g.submatrix id eqv.symm).det * h = 1 + (p : A) ^ m * r := by
  intro A K _ _ _ _ _ E _ _ c _ p R N _ Ω _ _ _ _ D σ m j k i bW bM eqv hqM hex
  refine ⟨?_, fun g hg => ?_⟩
  · have h3 : ∀ a : Fin k, ∃ x : Fin N → A, ∃ y ∈ D.omHT σ, D.q σ x = (bM a : Ω) + ((p : A) ^ m) • y := by
      intro a
      obtain ⟨x, y', hy', he⟩ := hex.2.2 (bM a) (bM a).2
      refine ⟨x, -y', Submodule.neg_mem _ hy', ?_⟩
      rw [he, smul_neg]
      abel
    choose xs ys hys hxs using h3
    refine ⟨Matrix.of fun l c => Sum.elim (fun a => i (bW a) l) (fun a => xs a l) c, fun a => ⟨0, ?_⟩,
      fun a => ⟨ys a, hys a, ?_⟩⟩
    · funext l
      simp
    · simpa using hxs a
  · have hsurj : ∀ x : Fin N → A, ∃ v : Fin j ⊕ Fin k → A, ∃ z : Fin N → A,
        x = g.mulVec v + ((p : A) ^ m) • z := by
      intro x
      obtain ⟨s, z, hz⟩ := frame_expand D hex hg x (bM.repr ⟨D.q σ x, hqM x⟩) 0 (Submodule.zero_mem _) (by
        rw [smul_zero, add_zero]
        have h5 := congrArg Subtype.val (bM.sum_repr ⟨D.q σ x, hqM x⟩)
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h5
        exact h5.symm)
      exact ⟨_, z, hz⟩
    choose v z hvz using fun l : Fin N => hsurj (Pi.single l 1)
    have hprod : g.submatrix id eqv.symm * Matrix.of (fun c l => v l (eqv.symm c)) =
        1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) := by
      ext l l'
      rw [Matrix.mul_apply]
      simp only [Matrix.submatrix_apply, id, Matrix.of_apply]
      have e1 : ∑ c, g l (eqv.symm c) * v l' (eqv.symm c) = (g.mulVec (v l')) l := by
        rw [Matrix.mulVec, dotProduct]
        exact Equiv.sum_comp eqv.symm (fun d => g l d * v l' d)
      rw [e1, eq_sub_of_add_eq (hvz l').symm]
      simp [Matrix.one_apply, Pi.single_apply]
    have hmem : (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A).det - 1 ∈
        Ideal.span {((p : A) ^ m)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, RingHom.map_det, sub_eq_zero]
      have e2 : (Ideal.Quotient.mk (Ideal.span {((p : A) ^ m)})).mapMatrix
          (1 - ((p : A) ^ m) • Matrix.of (fun l l' => z l' l) : Matrix (Fin N) (Fin N) A) = 1 := by
        ext a b
        rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub,
          map_mul, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), zero_mul, sub_zero,
          Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e2, Matrix.det_one]
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hmem
    refine ⟨(Matrix.of (fun c l => v l (eqv.symm c)) : Matrix (Fin N) (Fin N) A).det, r, ?_⟩
    rw [← Matrix.det_mul, hprod]
    linear_combination (-1 : A) * hr

end PositivityTheory.HtPt.Ge
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ra

theorem smith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j))) :=
  smith_of PositivityTheory.HtPt.Rh.aflat_fg PositivityTheory.HtPt.Rh.afquot

theorem cnt_coord : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) :=
  cnt_coord_of smith

theorem cnt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card N * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card N * (p - 1)) = cN ^ 2 → GenAF p AA.carrier ⊥) :=
  cnt_of cnt_coord

end PositivityTheory.HtPt.Ra
end
end
