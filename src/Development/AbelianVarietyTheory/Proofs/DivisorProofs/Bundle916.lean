module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle021
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle886
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle438
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle007
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isHolTo_congr_on {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} {B : Set V}
    {y y' : V → (Sp ℂ ⟶ X)} (h : ∀ b ∈ B, y b = y' b) : IsHolTo B y ↔ IsHolTo B y' := by
  have hs : ∀ U : X.Opens, {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ y' b ⁻¹ᵁ U} := fun U =>
    Set.ext fun b => ⟨fun ⟨hb, h'⟩ => ⟨hb, by rw [← h b hb]; exact h'⟩, fun ⟨hb, h'⟩ => ⟨hb, by rw [h b hb]; exact h'⟩⟩
  constructor
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [← hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩
  · intro H U s
    obtain ⟨h1, h2⟩ := H U s
    rw [hs U]
    exact ⟨h1, h2.congr fun b hb => by rw [h b hb.1]⟩

theorem unif_of_isBC : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R]
    (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (F' : Fam ℂ O Λ g),
    IsBC F' F σ → Nonempty (Unif F' (RingHom.id ℂ) ρ N C) → Nonempty (Unif F σ ρ N C) := by
  intro O _ bar g ρ R _ σ Λ F N C F' hbc hU
  obtain ⟨U'⟩ := hU
  obtain ⟨f, φ, hpb, hgp, hact, hL, heta⟩ := hbc
  have hw : φ ≫ F.A.hom = F'.A.hom ≫ f := hgp.1.w
  have hsq : f ≫ F.s = F'.s ≫ spMap σ := hpb.w
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := Spec.map_id _
  have hbase : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' h
    rw [Category.assoc, hsq, ← Category.assoc, h, hid, Category.id_comp]
  have hinj : ∀ y₁ y₂ : Sp ℂ ⟶ F'.X, y₁ ≫ F'.s = spMap (RingHom.id ℂ) → y₂ ≫ F'.s = spMap (RingHom.id ℂ) →
      y₁ ≫ f = y₂ ≫ f → y₁ = y₂ := fun y₁ y₂ h₁ h₂ h => hpb.hom_ext h (by rw [h₁, h₂])
  let exF : ∀ i P, (Fin g → ℂ) → (Over.mk (U'.u i P ≫ f) ⟶ F.A) := fun i P z =>
    Over.homMk ((U'.ex i P z).left ≫ φ) (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
  refine ⟨{
      n := U'.n, Di := U'.Di, t := U'.t, mem := U'.mem, ne := U'.ne, all := U'.all, distinct := U'.distinct
      u := fun i P => U'.u i P ≫ f, ex := exF, unif := ?_, onto := ?_, disj := ?_, fibre := ?_, hol := ?_, lift := ?_ }⟩
  · intro i P hP
    have h := U'.unif i P hP
    obtain ⟨e, he, hee⟩ := (GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ hgp hact hL heta (U'.Di i) (U'.t i) P
      (U'.u i P) h.1 (hbase _ h.1)).1 _ h
    have : e = exF i P := funext fun z => Over.OverMorphism.ext (by rw [hee z]; rfl)
    rw [← this]
    exact he
  · intro y hy
    obtain ⟨i, P, hP, hu⟩ := U'.onto (hpb.lift y (spMap (RingHom.id ℂ)) (by rw [hy, hid, Category.id_comp]))
      (IsPullback.lift_snd _ _ _ _)
    refine ⟨i, P, hP, ?_⟩
    show U'.u i P ≫ f = y
    rw [hu, IsPullback.lift_fst]
  · intro i j P P' hP hP' h
    exact U'.disj i j P P' hP hP' (hinj _ _ (U'.unif i P hP).1 (U'.unif j P' hP').1 h)
  · intro i P P' hP hP'
    refine Iff.trans ⟨fun h => hinj _ _ (U'.unif i P hP).1 (U'.unif i P' hP').1 h, fun h => ?_⟩ (U'.fibre i P P' hP hP')
    show U'.u i P ≫ f = U'.u i P' ≫ f
    rw [h]
  · intro i m B P hB hP
    obtain ⟨h1, h2⟩ := U'.hol i m B P hB hP
    refine ⟨(GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb (Fin m → ℂ) B (fun b => U'.u i (P b))
      (fun b hb => (U'.unif i (P b) (hP.1 b hb)).1)).1 h1, ?_⟩
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 φ
  · intro m B y hB hy hhol b₀ hb₀
    classical
    let y' : (Fin m → ℂ) → (Sp ℂ ⟶ F'.X) := fun b =>
      if h : y b ≫ F.s = spMap σ then hpb.lift (y b) (spMap (RingHom.id ℂ)) (by rw [h, hid, Category.id_comp])
      else hpb.lift (y b₀) (spMap (RingHom.id ℂ)) (by rw [hy b₀ hb₀, hid, Category.id_comp])
    have hy'1 : ∀ b ∈ B, y' b ≫ F'.s = spMap (RingHom.id ℂ) := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_snd _ _ _ _
    have hy'2 : ∀ b ∈ B, y' b ≫ f = y b := by
      intro b hb
      simp only [y', dif_pos (hy b hb)]
      exact IsPullback.lift_fst _ _ _ _
    have hh : IsHolTo B y' := (GlobalTheory.T.isHolTo_baseChange_complex_iff R σ F.X F'.X F.s F'.s f hpb _ B y' hy'1).2
      ((isHolTo_congr_on fun b hb => (hy'2 b hb).symm).1 hhol)
    obtain ⟨B', i, P, hB', hb', hsub, hP, hu⟩ := U'.lift m B y' hB hy'1 hh b₀ hb₀
    refine ⟨B', i, P, hB', hb', hsub, hP, fun b hb => ?_⟩
    show U'.u i (P b) ≫ f = y b
    rw [hu b hb, hy'2 b (hsub hb)]

end GlobalTheory.PELU
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.PELU

theorem spMap_id_complex : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
  simp [spMap]

theorem fineAt_of_isBC (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type)
    [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop)
    (F' : Fam ℂ O Λ g) (hBC : IsBC F' F σ) (hF : FineAt F σ ρ N C) : FineAt F' (RingHom.id ℂ) ρ N C := by
  obtain ⟨f, φ, pb, gp, hact, hL, heta⟩ := hBC
  have M := GlobalTheory.T.uniformisationAt_correspond_of_cartesian O bar g ρ R ℂ σ (RingHom.id ℂ) Λ F F' N f φ gp hact hL heta
  have base : ∀ y' : Sp ℂ ⟶ F'.X, y' ≫ F'.s = spMap (RingHom.id ℂ) → (y' ≫ f) ≫ F.s = spMap σ := by
    intro y' hy
    rw [Category.assoc, pb.w, ← Category.assoc, hy, spMap_id_complex, Category.id_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro y' hy
    obtain ⟨D', t, P, e, hC, hU⟩ := hF.pts (y' ≫ f) (base y' hy)
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy (base y' hy)).2 e hU
    exact ⟨D', t, P, e', hC, hU'⟩
  · intro D' t P hC hP
    obtain ⟨y, e, hU⟩ := hF.occ D' t P hC hP
    have w : y ≫ F.s = spMap (RingHom.id ℂ) ≫ spMap σ := by
      rw [hU.1, spMap_id_complex, Category.id_comp]
    obtain ⟨y', rfl, hy'⟩ : ∃ y', y' ≫ f = y ∧ y' ≫ F'.s = spMap (RingHom.id ℂ) :=
      ⟨pb.lift y _ w, pb.lift_fst _ _ w, pb.lift_snd _ _ w⟩
    obtain ⟨e', hU', -⟩ := (M D' t P y' hy' (base y' hy')).2 e hU
    exact ⟨y', e', hU'⟩
  · intro D' D'' t t' P P' y y' e e' hU hU' w h hw hP
    obtain ⟨e₁, hU₁, -⟩ := (M D' t P y hU.1 (base y hU.1)).1 e hU
    obtain ⟨e₂, hU₂, -⟩ := (M D'' t' P' y' hU'.1 (base y' hU'.1)).1 e' hU'
    have hf : y ≫ f = y' ≫ f := hF.sep D' D'' t t' P P' _ _ e₁ e₂ hU₁ hU₂ w h hw hP
    exact pb.hom_ext hf (hU.1.trans hU'.1.symm)

end GlobalTheory.PELU
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

noncomputable section

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ]

theorem isSplit_injective {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) : Function.Injective ι := by
  intro a b hab
  have := congrArg π hab
  rwa [h.1, h.1] at this

theorem inv_mul_mem_ker {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (γ : Γ) :
    (ι (π γ))⁻¹ * γ ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, h.1, inv_mul_cancel]

theorem commute_single {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (r : Γ) (hr : r ∈ π.ker) (c : ℂ) :
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c) := by
  refine MonoidAlgebra.induction_on (motive := fun x =>
    Commute (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x) (MonoidAlgebra.single r c)) x ?_ ?_ ?_
  · intro m
    show _ * _ = _ * _
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, h.2 m r hr]
  · intro x y hx hy
    rw [map_add (f := _)]
    exact hx.add_left hy
  · intro a x hx
    rw [map_smul]
    exact hx.smul_left a

theorem asAlgebraHom_map {V : Type} [AddCommGroup V] [Module ℂ V] (ι : G →* Γ)
    (ρ : Representation ℂ Γ V) (e : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e := by
  refine MonoidAlgebra.induction_on (motive := fun e =>
    ρ.asAlgebraHom (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι e) =
      Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) e ?_ ?_ ?_
  · intro m
    simp [MonoidAlgebra.of_apply, Representation.asAlgebraHom_single]
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  · intro a x hx
    rw [map_smul, map_smul, map_smul, hx]

variable [Fintype Γ]

def eR (π : Γ →* G) : MonoidAlgebra ℂ Γ :=
  ∑ r : π.ker, MonoidAlgebra.single (r : Γ) ((Nat.card π.ker : ℂ)⁻¹)

theorem coeff_map_mul_eR {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (x : MonoidAlgebra ℂ G)
    (γ : Γ) :
    (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x * eR π).coeff γ =
      x.coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
  unfold eR
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [MonoidAlgebra.mul_single_apply]
  let r0 : π.ker := ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩
  have key : ∀ r : π.ker, (MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι x).coeff (γ * (r : Γ)⁻¹) =
      if r = r0 then x.coeff (π γ) else 0 := by
    intro r
    rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.coeff_mapDomain]
    split_ifs with hr
    · have : γ * (r : Γ)⁻¹ = ι (π γ) := by
        subst hr
        simp [r0]
      rw [this, Finsupp.mapDomain_apply_of_injective (isSplit_injective h)]
    · apply Finsupp.mapDomain_notin_range
      rintro ⟨g, hg⟩
      apply hr
      have hr1 : π (r : Γ) = 1 := r.2
      have hg' : g = π γ := by
        have := congrArg π hg
        rwa [h.1, map_mul, map_inv, hr1, inv_one, mul_one] at this
      subst hg'
      apply Subtype.ext
      show (r : Γ) = (ι (π γ))⁻¹ * γ
      rw [hg]
      group
  simp_rw [key, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def comapEquiv {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    P × π.ker ≃ P.comap π where
  toFun x := ⟨ι x.1 * x.2, by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    simp [Subgroup.mem_comap, h.1, hr1]⟩
  invFun γ := (⟨π γ, γ.2⟩, ⟨(ι (π γ))⁻¹ * γ, inv_mul_mem_ker h γ⟩)
  left_inv x := by
    have hr1 : π (x.2 : Γ) = 1 := x.2.2
    ext <;> simp [h.1, hr1]
  right_inv γ := by
    ext
    simp

theorem card_comap {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G) :
    Nat.card (P.comap π) = Nat.card P * Nat.card π.ker := by
  rw [← Nat.card_prod]
  exact (Nat.card_congr (comapEquiv h P)).symm

end GlobalTheory.BadCount.Lift

namespace GlobalTheory.BadCount.Lift

open scoped Classical

variable {G Γ : Type} [Group G] [Group Γ] [Fintype Γ]

theorem lvlIdem_comap [Fintype G] {π : Γ →* G} {ι : G →* Γ} (h : IsSplit π ι) (P : Subgroup G)
    (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ) (hl : ∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) :
    Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι (Formalism.L2.DIV.lvlIdem P lam) * eR π := by
  have hcard := card_comap h P

  simp only [Formalism.L2.DIV.lvlIdem, eR, map_sum, MonoidAlgebra.mapDomainAlgHom_apply,
  MonoidAlgebra.mapDomain_single, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single]
  rw [← Fintype.sum_prod_type' (f := fun (i : P) (j : π.ker) =>
    MonoidAlgebra.single (ι (i : G) * (j : Γ))
      ((Nat.card P : ℂ)⁻¹ * ((lam i⁻¹ : ℂˣ) : ℂ) * (Nat.card π.ker : ℂ)⁻¹))]
  refine (Fintype.sum_equiv (comapEquiv h P) _ _ (fun x => ?_)).symm
  have hr1 : π (x.2 : Γ) = 1 := x.2.2
  have hx : lamb ((comapEquiv h P) x)⁻¹ = lam x.1⁻¹ := by
    rw [hl]
    congr 1
    apply Subtype.ext
    simp [comapEquiv, h.1, hr1]
  simp only [hx, hcard, Nat.cast_mul, mul_inv]
  congr 1
  ring

end GlobalTheory.BadCount.Lift


open scoped Classical in
theorem GlobalTheory.BadCount.finrank_eig_inf_ker_le_of_isSplit : ∀ (G Γ V : Type) [Group G] [Fintype G] [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Γ →* G) (ι : G →* Γ), IsSplit π ι → ∀ (ρ : Representation ℂ Γ V) (P : Subgroup G) (lam : P →* ℂˣ) (lamb : P.comap π →* ℂˣ), (∀ γ : P.comap π, lamb γ = lam ⟨π γ, γ.2⟩) → ∀ (H : Fin 2 → Subgroup G) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ G) (b : Fin 2 → MonoidAlgebra ℂ G) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ ((H k).comap π) (n k)) → (∀ k, (n k : ℝ) * Nat.card ((H k).comap π) ≤ c * Nat.card (P.comap π) * finrank ℂ (eig ρ (P.comap π) lamb)) → (∀ k, b k * b k = b k) → (∀ k a, b k * a = a * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem P lam).coeff 1 = (s k : ℂ) / (Nat.card P : ℂ)) → (finrank ℂ (eig ρ (P.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp ι : Representation ℂ G V) e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ (P.comap π) lamb) := by
  intro G Γ V _ _ _ _ _ _ _ π ι h ρ P lam lamb hl H n e b s c hEmb hcard hidem hcent hsum hsupp hcoeff
  let ιA := MonoidAlgebra.mapDomainAlgHom ℂ ℂ ι
  have hL := GlobalTheory.BadCount.Lift.lvlIdem_comap h P lam lamb hl
  have hR : (Nat.card π.ker : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hP : (Nat.card P : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hprod : ∀ k, ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb =
      ιA (b k * Formalism.L2.DIV.lvlIdem P lam) * GlobalTheory.BadCount.Lift.eR π := by
    intro k
    rw [hL, map_mul, mul_assoc]
  have hco : ∀ k γ, (ιA (b k) * Formalism.L2.DIV.lvlIdem (P.comap π) lamb).coeff γ =
      (b k * Formalism.L2.DIV.lvlIdem P lam).coeff (π γ) * (Nat.card π.ker : ℂ)⁻¹ := by
    intro k γ
    rw [hprod]
    exact GlobalTheory.BadCount.Lift.coeff_map_mul_eR h _ γ
  have key := GlobalTheory.T.finrank_characterEigenspace_inf_ker_le Γ V ρ (P.comap π) lamb (fun k => (H k).comap π) n (ιA e) (fun k => ιA (b k)) s c
    hEmb hcard
    (fun k => by rw [← map_mul, hidem])
    (fun k => by
      rw [hL]
      refine Commute.mul_right ?_ ?_
      · exact Commute.map (show Commute (b k) (Formalism.L2.DIV.lvlIdem P lam) from hcent k _) ιA
      · unfold GlobalTheory.BadCount.Lift.eR
        refine Commute.sum_right _ _ _ (fun r _ => ?_)
        exact GlobalTheory.BadCount.Lift.commute_single h _ r r.2 _)
    (by rw [← map_one ιA, ← map_sub, hsum, map_sub, map_add (f := _), map_mul])
    (fun k γ hne => by
      rw [hco] at hne
      show π γ ∈ H k
      apply hsupp k
      intro h0
      apply hne
      rw [h0, zero_mul])
    (fun k => by
      rw [hco, map_one, hcoeff, GlobalTheory.BadCount.Lift.card_comap h P, Nat.cast_mul]
      field_simp)
  rwa [GlobalTheory.BadCount.Lift.asAlgebraHom_map] at key
end
end

section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

variable {F : Type} [Field F] {r : ℕ}

section Nonvanishing

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

end Nonvanishing

section Embedding

variable {d d' : ℕ}

variable (b : Fin r → ℕ) (c : ℕ)

end Embedding

section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

theorem leviWh_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first
  | exact @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | (apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one ..)

end Main

end GlobalTheory.FinGL.LeviWh
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.EtFromConn

variable {p : ℕ} [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn))

theorem dual_conn {k : Type} [Field k] [CharP k p] [PerfectRing k p] {G : PDivGroup p k}
    (hG : G.IsEt) : G.dual.IsConn :=
  PDivGroup.dual_isConn_of_isEt p k G hG

abbrev Mod {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k)
    (hG : G.IsEt) : Type :=
  Module.Dual (WittVector p k) (B.M G.dual (dual_conn hG))

def IsTr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] (σ : k →+* k') {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (l' : Mod B G' hG') : Prop :=
  letI : Algebra k k' := σ.toAlgebra
  ∃ (hb : (G.dual.baseChange k').IsConn)
    (lb : Module.Dual (WittVector p k') (B.M (G.dual.baseChange k') hb)),
    (∀ x, lb (B.smap hb (dual_conn hG) (G.dual.toBase k') x) = WittVector.map σ (l x)) ∧
    ∀ y, l' y = lb (B.map hb (dual_conn hG')
      ((PerfdLat.dualBaseChange k' G).inv ≫ dualHom G' (G.baseChange k') s.lift) y)


open Classical in
def tr {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) : Mod B G' hG' :=
  if h : ∃ l', IsTr B σ hG' hG s l l' then Classical.choose h else 0

theorem tr_spec {k k' : Type} [Field k] [CharP k p] [PerfectRing k p] [Field k'] [CharP k' p]
    [PerfectRing k' p] {σ : k →+* k'} {G' : PDivGroup p k'} {G : PDivGroup p k} (hG' : G'.IsEt)
    (hG : G.IsEt) (s : SemiHom σ G' G) (l : Mod B G hG) (h : ∃ l', IsTr B σ hG' hG s l l') :
    IsTr B σ hG' hG s l (tr B hG' hG s l) := by
  rw [tr, dite_eq_left h]
  exact Classical.choose_spec h

section Red

variable {k : Type} [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (hG : G.IsEt)

theorem exists_redDual : ∃ r' : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
      Module.Dual k G.dual.RigExt,
    (∀ l m, r' l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective r' ∧ ∀ l, r' l = 0 ↔ ∃ l', l = p • l' := by
  haveI := B.free G.dual (dual_conn hG)
  haveI := B.finite G.dual (dual_conn hG)
  exact wittDual_reduction p k _ _ (B.red G.dual (dual_conn hG))
    (B.red_surjective G.dual (dual_conn hG)) (B.red_eq_zero G.dual (dual_conn hG))

def redDual : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)]
    Module.Dual k G.dual.RigExt :=
  Classical.choose (exists_redDual B G hG)

theorem redDual_spec :
    (∀ l m, redDual B G hG l (B.red G.dual (dual_conn hG) m) = WittVector.constantCoeff (l m)) ∧
      Function.Surjective (redDual B G hG) ∧ ∀ l, redDual B G hG l = 0 ↔ ∃ l', l = p • l' :=
  Classical.choose_spec (exists_redDual B G hG)

def rigLie : G.RigExt ≃ₗ[k] G.dual.Lie :=
  LinearEquiv.ofBijective (G.rigToLie (p_eq_zero p k))
    (PDivGroup.rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt p k (p_eq_zero p k) G hG).1

def red : Mod B G hG →ₛₗ[(WittVector.constantCoeff : WittVector p k →+* k)] G.RigExt :=
  (rigLie G hG).symm.toLinearMap.comp (G.dual.rigOfOmega.dualMap.comp (redDual B G hG))

theorem rigToLie_red (l : Mod B G hG) :
    G.rigToLie (p_eq_zero p k) (red B G hG l) = G.dual.rigOfOmega.dualMap (redDual B G hG l) :=
  (rigLie G hG).apply_symm_apply _

end Red

end GlobalTheory.Dieu.EtFromConn
end
end
