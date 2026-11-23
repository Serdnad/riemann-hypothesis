module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle004
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle009
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle007
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle012
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Valuation.Integers
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
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.DualLattices.ProdDvdOfIso
public import ReciprocityTheory.DualLattices.Bundle012
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

section

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {p R N : ℕ}
  {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
  (D : HTChart A K c p R N Ω)

theorem om'_le : D.om' ≤ D.om := by
  refine sup_le (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact D.h_mem x
  · rintro _ ⟨x, hx, rfl⟩
    exact D.om.smul_mem _ hx

theorem pow_smul_mem {x : Ω} (hx : x ∈ D.om) : ((p : A) ^ R) • x ∈ D.om' :=
  Submodule.mem_sup_right ⟨x, hx, rfl⟩

theorem h_mem_om' (x : Fin N → 𝓞 E) : D.h x ∈ D.om' :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨x, rfl⟩)

theorem ht_mem_span {C O : Type} [Field C] [CommRing O] [Algebra O C] {κ' : O}
    {V Ω' : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω'] [Module C Ω'] [Module O Ω'] [IsScalarTower O C Ω']
    (φ : A →+* O) (P : HTPoint C O c κ' N V Ω') (ι : D.om →ₛₗ[φ] Ω') (hred : D.ReducesTo φ P ι)
    {t : V} (ht : t ∈ P.T) :
    P.ht t ∈ Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) := by
  classical
  set S := Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'})
  have hp : ∀ y ∈ P.om, (p ^ R) • y ∈ S := by
    intro y hy
    rw [← hred.span_eq] at hy
    induction hy using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      refine Submodule.subset_span ⟨(p ^ R) • m, ?_, map_nsmul ι _ _⟩
      have := pow_smul_mem D m.2
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
      exact this
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact S.add_mem ha hb
    | smul a w _ hw => rw [smul_comm]; exact S.smul_mem a hw
  have hT : P.T ≤ S.comap (P.ht.restrictScalars O) := by
    rw [P.free.2.2, Submodule.span_le]
    rintro _ ⟨⟨i, k⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := hred.ht_eq (Pi.single i (RingOfIntegers.basis E k))
    have h1 : P.tate (Pi.single i (RingOfIntegers.basis E k)) =
        P.ρ (RingOfIntegers.basis E k) (P.t i) := by
      rw [HTPoint.tate, Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [h1] at he
    change P.ht (P.ρ (RingOfIntegers.basis E k) (P.t i)) ∈ S
    rw [← sub_eq_iff_eq_add.2 he]
    exact S.sub_mem (Submodule.subset_span ⟨_, h_mem_om' D _, rfl⟩) (hp y hy)
  exact hT ht

end

theorem chart_ii : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N hp Ω _ _ _ _ D κ hκ hP hT
  refine ⟨om'_le D, fun x hx => ?_⟩
  have hp0 : algebraMap A K ((p : A) ^ R) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  have hlat : D.om'.IsFullLattice K := by
    letI : D.om'.IsLattice K :=
      Submodule.IsLattice.of_fg K (Submodule.FG.of_le D.om_lat.fg (om'_le D))
    refine ⟨?_⟩
    apply top_unique
    rw [← D.om_lat.span_eq_top]
    apply Submodule.span_le.2
    intro x hx
    have hh := Submodule.subset_span (R := K) (pow_smul_mem D hx)
    rw [← IsScalarTower.algebraMap_smul K] at hh
    have hh' := (Submodule.span K (D.om' : Set Ω)).smul_mem
      (algebraMap A K ((p : A) ^ R))⁻¹ hh
    simpa [smul_smul, hp0] using hh'
  refine test_incl A K Ω D.om' _ hlat hP fun q hq h1 => ?_
  by_cases hpq : (p : A) ∈ q
  swap
  · refine ⟨(p : A) ^ R, fun h => hpq (hq.mem_of_pow_mem R h), ?_⟩
    exact pow_smul_mem D (D.om.smul_mem κ hx)
  obtain ⟨C, O, _, _, _, _, _, v, φ, V, Ω', _, _, _, _, _, _, _, _, P, ι, hv, hφ, hcen, hred⟩ :=
    hT q hq h1 hpq
  letI : Algebra A O := φ.toAlgebra
  obtain ⟨j, hj, -, hj1⟩ := bc_iso A K Ω D.om C v O hv Ω' P.om ι D.om_lat D.om_proj P.om_lat
    hred.span_eq hred.rank_eq
  obtain ⟨s, hs, hsx⟩ := test_descend A K C v O hv q D.om (D.om'.comap D.om.subtype)
    (κ • ⟨x, hx⟩) hq h1 hφ hcen (by
      obtain ⟨t, ht, hte⟩ := P.κ_mem (ι ⟨x, hx⟩)
        (hred.span_eq ▸ Submodule.subset_span ⟨_, rfl⟩)
      have h2 := ht_mem_span D φ P ι hred ht
      rw [hte, ← ι.map_smulₛₗ, ← hj1] at h2
      have h3 : Submodule.span O (ι '' {x : D.om | (x : Ω) ∈ D.om'}) =
          (Submodule.span O ((fun y : D.om => (1 : O) ⊗ₜ[A] y) ''
            (D.om'.comap D.om.subtype : Set D.om))).map j := by
        rw [Submodule.map_span, Set.image_image]
        simp only [hj1]
        rfl
      rw [h3] at h2
      obtain ⟨z, hz, hze⟩ := h2
      rwa [← hj hze])
  exact ⟨s, hs, hsx⟩

end PositivityTheory.HtPt.Gc
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace PositivityTheory.HtPt.Twpol

open Coalgebra WithConv

section Level

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Module.Finite O A] [Module.Projective O A]
  {J : Type} (x : J → A →ₐ[O] O)

abbrev fm (a : J) : CartierDual O A := toConv (x a).toLinearMap

theorem sep_two (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g) (s t : A ⊗[O] A)
    (h : ∀ a b, CartierDual.pair O A A (fm x a ⊗ₜ fm x b) s = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) t) :
    s = t := by
  have hr : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      φ (TensorProduct.rid O A (LinearMap.lTensor A ψ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp [mul_comm]
  have hl : ∀ (φ ψ : CartierDual O A) (s : A ⊗[O] A),
      ψ (TensorProduct.lid O A (LinearMap.rTensor A φ.ofConv s)) = CartierDual.pair O A A (φ ⊗ₜ ψ) s := by
    intro φ ψ s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul a b => simp
  refine CartierDual.tensor_eq_of_forall_pair fun φ ψ => ?_
  rw [← hl, ← hl]
  refine congrArg _ (sep _ _ fun b => ?_)
  refine (hl φ (fm x b) s).trans (Eq.trans ?_ (hl φ (fm x b) t).symm)
  rw [← hr, ← hr]
  refine congrArg _ (sep _ _ fun a => ?_)
  exact (hr (fm x a) (fm x b) s).trans ((h a b).trans (hr (fm x a) (fm x b) t).symm)

theorem exists_bialgHom [AddCommGroup J] (sep : ∀ f g : A, (∀ a, x a f = x a g) → f = g)
    (h0 : fm x 0 = 1) (hadd : ∀ a b, fm x (a + b) = fm x a * fm x b)
    (l : CartierDual O A →ₗ[O] A) (u : J → A) (hl : ∀ a φ, x a (l φ) = φ (u a))
    (hu0 : ∀ b, x b (u 0) = 1) (hu0' : ∀ a, x 0 (u a) = 1)
    (hua : ∀ a a' b, x b (u (a + a')) = x b (u a) * x b (u a'))
    (hub : ∀ a b b', x (b + b') (u a) = x b (u a) * x b' (u a)) :
    ∃ lam : CartierDual O A →ₐc[O] A, ∀ φ, lam φ = l φ := by
  have hx0 : ∀ f, x 0 f = counit (R := O) f := fun f => congrArg (fun φ : CartierDual O A => φ f) h0
  have hxa : ∀ a b f, x (a + b) f = CartierDual.pair O A A (fm x a ⊗ₜ fm x b) (comul f) := fun a b f =>
    (congrArg (fun φ : CartierDual O A => φ f) (hadd a b)).trans (CartierDual.mul_apply _ _ _)
  have hone : u 0 = 1 := sep _ _ fun b => by rw [hu0, map_one]
  have hmul : ∀ a a', u (a + a') = u a * u a' := fun a a' => sep _ _ fun b => by rw [hua, map_mul]
  have hco : ∀ a, comul (R := O) (u a) = u a ⊗ₜ u a := fun a => sep_two x sep _ _ fun b b' => by
    rw [← hxa, hub, CartierDual.pair_tmul_tmul]; rfl
  let F : CartierDual O A →ₐ[O] A := AlgHom.ofLinearMap l
    (sep _ _ fun a => by rw [hl, map_one, CartierDual.one_apply, ← hx0, hu0'])
    (fun φ ψ => sep _ _ fun a => by
      rw [map_mul (x a), hl, hl, hl, CartierDual.mul_apply, hco, CartierDual.pair_tmul_tmul])
  have hF : ∀ φ, F φ = l φ := fun _ => rfl
  refine ⟨BialgHom.ofAlgHom F (AlgHom.ext fun φ => ?_) (AlgHom.ext fun φ => ?_), fun φ => rfl⟩
  · change counit (R := O) (l φ) = counit (R := O) φ
    rw [← hx0, hl, hone, CartierDual.counit_apply]
  · change Algebra.TensorProduct.map F F (comul (R := O) φ) = comul (R := O) (l φ)
    refine sep_two x sep _ _ fun a b => ?_
    rw [← hxa, hl, hmul, ← CartierDual.pair_comul_tmul]
    generalize comul (R := O) φ = s
    induction s with
    | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy]
    | tmul φ ψ =>
      rw [Algebra.TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul, ← hl, ← hl]
      rfl

end Level

theorem exists_linear {O A T J : Type} [CommRing O] [CommRing A] [Algebra O A] (S : Subalgebra O (T → O))
    (e : A ≃ₐ[O] S) (q : J → T) (x : J → A →ₐ[O] O) (hx : ∀ a f, x a f = (e f).1 (q a))
    (s : T × T → O) (hs : s ∈ Submodule.span O {g | ∃ a ∈ S, ∃ b ∈ S, g = fun z : T × T => a z.1 * b z.2}) :
    ∃ (l : CartierDual O A →ₗ[O] A) (u : J → A),
      (∀ a φ, x a (l φ) = φ (u a)) ∧ ∀ a b, x b (u a) = s (q a, q b) := by
  induction hs using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨f, hf, g, hg, rfl⟩ := hg
    refine ⟨(CartierDual.evalAt O A (e.symm ⟨g, hg⟩)).smulRight (e.symm ⟨f, hf⟩),
      fun a => f (q a) • e.symm ⟨g, hg⟩, fun a φ => ?_, fun a b => ?_⟩
    · rw [LinearMap.smulRight_apply, map_smul, map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul,
        mul_comm]
      rfl
    · rw [map_smul, hx, AlgEquiv.apply_symm_apply, smul_eq_mul]
  | zero => exact ⟨0, 0, by simp, by simp⟩
  | add s t _ _ hs ht =>
    obtain ⟨l, u, h1, h2⟩ := hs
    obtain ⟨l', u', h1', h2'⟩ := ht
    exact ⟨l + l', u + u', by simp [h1, h1'], by simp [h2, h2']⟩
  | smul c s _ hs =>
    obtain ⟨l, u, h1, h2⟩ := hs
    exact ⟨c • l, c • u, by simp [h1], by simp [h2]⟩

theorem tower_pol : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t := Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧ ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := exists_linear (X.A n) (e n) (lev p n) (fun a => (τ a).pt n)
      (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := exists_bialgHom (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add]) (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ

end PositivityTheory.HtPt.Twpol
end
end

section

noncomputable section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Ra

section Count

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

lemma monomialCount_col_mem_span {X : Type} [Fintype X] (B' : Matrix X X C) (V : Matrix X X R)
    (j : X) :
    (fun x => (B' * V.map (algebraMap R C)) x j) ∈
      Submodule.span R (Set.range fun α x => B' x α) := by
  have h : (fun x => (B' * V.map (algebraMap R C)) x j) = ∑ α, V α j • (fun x => B' x α) := by
    ext x
    simp [Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  rw [h]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)

lemma monomialCount_exists_factor {X : Type} [Fintype X] (B B' : Matrix X X C)
    (h : ∀ α, (fun x => B' x α) ∈ Submodule.span R (Set.range fun j x => B x j)) :
    ∃ W : Matrix X X R, B' = B * W.map (algebraMap R C) := by
  choose c hc using fun α => (Submodule.mem_span_range_iff_exists_fun R).1 (h α)
  refine ⟨fun i α => c α i, ?_⟩
  ext x α
  have := congrFun (hc α) x
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, Algebra.smul_def] at this
  rw [← this, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma monomialCount_prod_pow_mem {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
    (A : HopfOrder (C := C) R N) {ι : Type} [Fintype ι] (f : ι → N → C)
    (hf : ∀ j, f j ∈ A.carrier) (n : ι → ℕ) : (fun y => ∏ j, f j y ^ n j) ∈ A.carrier := by
  have hpow : ∀ j k, f j ^ k ∈ A.carrier := by
    intro j k
    induction k with
    | zero => simpa using A.one_mem
    | succ k ih => rw [pow_succ]; exact A.mul_mem _ _ ih (hf j)
  have : (fun y => ∏ j, f j y ^ n j) = ∏ j, f j ^ n j := by
    ext y; simp [Finset.prod_apply]
  rw [this]
  exact Finset.prod_induction _ (· ∈ A.carrier) (fun a b ha hb => A.mul_mem a b ha hb)
    A.one_mem (fun j _ => hpow j (n j))

end Count

lemma monomialCount_exponent (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → NNReal) :
    (∏ j, a j) ^ (Fintype.card (ι → ZMod p) * (p - 1)) =
      (∏ j, a j ^ (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2))) ^ 2 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  have h2 : p * (p - 1) / 2 * 2 = p * (p - 1) :=
    Nat.div_mul_cancel (Nat.even_mul_pred_self p).two_dvd
  have h3 : p ^ (Fintype.card ι - 1) * p = p ^ Fintype.card ι := by
    rw [← pow_succ, Nat.sub_add_cancel hpos]
  have hcard : Fintype.card (ι → ZMod p) = p ^ Fintype.card ι := by
    simp [ZMod.card]
  rw [Finset.prod_pow, ← pow_mul, hcard]
  congr 1
  calc p ^ Fintype.card ι * (p - 1) = p ^ (Fintype.card ι - 1) * p * (p - 1) := by rw [h3]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1)) := by ring
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2 * 2) := by rw [h2]
    _ = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) * 2 := by ring

theorem cnt_coord_of (hsmith : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∃ (Λ : Matrix ι ι R) (ε : ι → R), IsUnit Λ.det ∧ afLat p AA.carrier = Submodule.span R (Set.range fun j => ε j • Λ j) ∧ (∀ j, v (p : C) ≤ v (algebraMap R C (ε j)) ^ (p - 1)) ∧ HasLen v R (AFQuot p AA.carrier) (∏ j, v (algebraMap R C (ε j)))) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (AA : HopfOrder (C := C) R (ι → ZMod p)), ∀ cA cN, HasLen v R (AFQuot p AA.carrier) cA → HasColen R v AA.carrier cN → cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) ≤ cN ^ 2 ∧ (cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = cN ^ 2 → ∃ x : ι → (ι → ZMod p) → C, (∀ j, x j ∈ afFun p AA.carrier) ∧ AA.carrier = Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) => ∏ j, x j y ^ (α j).val)) := by
  intro p _ C _ _ _ v R _ _ hv hp1 ι _ _ AA cA cN hA hN
  obtain ⟨Λ, ε, hΛ, hspan, hε, hlen⟩ := hsmith p C v R hv hp1 ι AA
  have hcA : cA = ∏ j, v (algebraMap R C (ε j)) := hasLen_unique hv hA hlen
  have hl := fun j => lifts p C v R hv hp1 ι AA (Λ j) (ε j)
    (by rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩) (hε j)
  choose u hu_mem hu_int hu_cong using hl

  let B' : Matrix (ι → ZMod p) (ι → ZMod p) C := Matrix.of fun (x α : ι → ZMod p) =>
    ∏ j, (algebraMap R C (ε j) * u j x) ^ (α j).val
  have hB'v : v B'.det = ∏ j, v (algebraMap R C (ε j)) ^
      (p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2)) :=
    (u5 p C v R hv hp1 ι Λ u hΛ hu_int hu_cong).2 fun j => algebraMap R C (ε j)
  have hsq : cA ^ (Fintype.card (ι → ZMod p) * (p - 1)) = v B'.det ^ 2 := by
    rw [hcA, hB'v]
    exact monomialCount_exponent p _

  have hp0 : v (p : C) ≠ 0 :=
    (Valuation.ne_zero_iff v).2 (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hε0 : ∀ j, v (algebraMap R C (ε j)) ≠ 0 := by
    intro j h0
    have hpp : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    have := hε j
    rw [h0, zero_pow hpp] at this
    exact hp0 (le_antisymm this zero_le)
  have hB'0 : v B'.det ≠ 0 := by
    rw [hB'v]
    exact Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hε0 j)

  have hmem : ∀ α : ι → ZMod p, (fun x => B' x α) ∈ AA.carrier := by
    intro α
    exact monomialCount_prod_pow_mem AA (fun j y => algebraMap R C (ε j) * u j y)
      (fun j => (Submodule.mem_inf.1 (hu_mem j)).1) (fun j => (α j).val)
  obtain ⟨B, hAA, hBc⟩ := hN
  obtain ⟨W, hW⟩ := monomialCount_exists_factor (R := R) B B' (fun α => hAA ▸ hmem α)
  have hdet : v B'.det = cN * v (algebraMap R C W.det) := by
    rw [hW, Matrix.det_mul, map_mul, RingHom.map_det, hBc]; rfl
  have hw1 : v (algebraMap R C W.det) ≤ 1 := hv.map_le_one W.det
  have hle : v B'.det ≤ cN := by
    rw [hdet]; exact mul_le_of_le_one_right zero_le hw1
  refine ⟨by rw [hsq]; exact pow_le_pow_left₀ zero_le hle 2, fun heq => ?_⟩
  have hBeq : v B'.det = cN := by
    rw [hsq] at heq
    exact (pow_left_inj₀ zero_le zero_le two_ne_zero).1 heq
  have hcN0 : cN ≠ 0 := hBeq ▸ hB'0
  have hw : v (algebraMap R C W.det) = 1 := by
    have h : cN * v (algebraMap R C W.det) = cN * 1 := by rw [← hdet, hBeq, mul_one]
    exact mul_left_cancel₀ hcN0 h
  have hWu : IsUnit W.det :=
    hv.isUnit_of_one (isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hw) hw
  have hBeq' : B' * (W⁻¹).map (algebraMap R C) = B := by
    rw [hW, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hWu,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
  refine ⟨fun j y => algebraMap R C (ε j) * u j y, hu_mem, ?_⟩
  have hspan' : Submodule.span R (Set.range fun (α : ι → ZMod p) (y : ι → ZMod p) =>
      ∏ j, (algebraMap R C (ε j) * u j y) ^ (α j).val) =
      Submodule.span R (Set.range fun α x => B' x α) := rfl
  rw [hspan']
  refine le_antisymm ?_ (Submodule.span_le.2 ?_)
  · rw [hAA]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have := monomialCount_col_mem_span (R := R) B' (W⁻¹) j
    rwa [hBeq'] at this
  · rintro _ ⟨α, rfl⟩
    exact hmem α

end PositivityTheory.HtPt.Ra
end
end

section

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace PositivityTheory.HtPt.Gd

theorem free_of_fg {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
    (L : Submodule O Ω) (hL : L.FG) : Module.Free O L := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL
  haveI : Module.Flat O L := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have hx0 : (a : O) • (x : Ω) = 0 := by
      have := congrArg Subtype.val ha
      simpa [Submonoid.smul_def] using this
    rw [← algebraMap_smul C (a : O) (x : Ω), smul_eq_zero] at hx0
    rcases hx0 with h | h
    · exact absurd (hv.hom_inj (h.trans (map_zero _).symm)) (nonZeroDivisors.coe_ne_zero a)
    · exact (Submodule.mem_bot O).mpr (Subtype.ext (by simpa using h))
  exact Module.free_of_flat_of_isLocalRing

end PositivityTheory.HtPt.Gd
end
end
