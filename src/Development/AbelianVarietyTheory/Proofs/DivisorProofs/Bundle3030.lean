module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.SFour

theorem pow_le_map {V V' : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [CommRing V'] [IsLocalRing V']
    (io : V →+* V') (hfin : io.Finite) :
    ∃ J : ℕ, ∀ j : ℕ, maximalIdeal V' ^ (J * j) ≤ (maximalIdeal V ^ j).map io := by
  letI := io.toAlgebra
  haveI : Module.Finite V V' := hfin
  obtain ⟨E, hE⟩ := GlobalTheory.Poinc.OrbTrace.exists_pow_le (A := V) (B := V') (maximalIdeal V') (maximalIdeal.isMaximal V') 1
  have h1 : maximalIdeal V' ^ E ≤ (maximalIdeal V).map io := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hE x hx
    have hu' : IsUnit u := by
      by_contra h
      exact hu ((IsLocalRing.mem_maximalIdeal _).2 h)
    rw [pow_one] at hux
    exact (Ideal.unit_mul_mem_iff_mem _ hu').1 hux
  refine ⟨E, fun j => ?_⟩
  rw [pow_mul, Ideal.map_pow]
  exact Ideal.pow_right_mono h1 j

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A]
  [IsLocalRing A]

theorem term_mem (Φ : VPre bar q W A) (y : Φ.Y) (mu : Fin s → Φ.X y) (cc : Φ.Q) (j : ℕ)
    (hj : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) : Φ.term y mu cc ∈ maximalIdeal (Φ.V y) ^ j := by
  have hnn : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have hle : j ≤ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    have e1 : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (hnn i)
    rw [← e1] at hj
    exact_mod_cast hj
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle ?_)
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _

end GlobalTheory.Poinc.SFour

namespace GlobalTheory.Poinc.SFour

theorem four_of_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.ClassSums N₁ → Φ.Four N₁ := by
  intro O _ bar q s W A _ _ _ _ Φ N₁ hcs y₀ N₀
  classical
  obtain ⟨N, hN0, hN1, hNd, k, hk0, hk, L, _, _, _, _, _, _, 𝔷, f, hz, hf, hy, hσ⟩ := hcs y₀ N₀
  refine ⟨N, hN0, hNd, k, hk0, hk, fun l a c e => ?_⟩
  obtain ⟨C, hC1, hC2, hC3⟩ := OrbTrace.exists_classes (O := O) (N₁ := N₁) hN1 a
  set F : integralClosure A L := ∑ c' ∈ C, ∏ i, f (fun u => c' (i, u)) (c i) with hF
  have hFix : ∀ σ : L ≃ₐ[FractionRing A] L, (∀ x x' : integralClosure A L, (x' : L) = σ x → (x ∈ 𝔷 ↔ x' ∈ 𝔷)) →
      σ (F : L) = F := by
    intro σ hσ'
    obtain ⟨ga, h1, h2, h3, h4⟩ := hσ σ hσ'
    have e1 : ((F : integralClosure A L) : L) = ∑ c' ∈ C, ∏ i, (f (fun u => c' (i, u)) (c i) : L) := by
      rw [hF]; push_cast; rfl

    rw [e1, map_sum]
    simp only [map_prod, h4]
    exact OrbTrace.sum_comp_eq C hC1 hC2 hC3 ga h1 h2 h3 (fun c' => ∏ i, (f (fun u => c' (i, u)) (c i) : L))
      (fun c₁ c₂ h => Finset.prod_congr rfl fun i _ => by rw [hf _ _ _ fun u => h _])
  haveI := hz
  obtain ⟨g₀, b, hb, hbF⟩ := GlobalTheory.DecompFixed.exists_approx_integralClosure A (FractionRing A) L 𝔷 F hFix e
  refine ⟨g₀, fun y j => ?_⟩
  obtain ⟨V', _, _, io, ev', hfin, hloc, hpure, hcomm, hcomap, hcls⟩ := hy y
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  obtain ⟨J, hJ⟩ := pow_le_map io hfin
  set j' := J * j + j with hj'
  have hjj : j ≤ j' := Nat.le_add_left _ _
  have hJj : maximalIdeal V' ^ j' ≤ (maximalIdeal (Φ.V y) ^ j).map io :=
    (Ideal.pow_le_pow_right (Nat.le_add_right _ _)).trans (hJ j)
  have hmap : ∀ n, (maximalIdeal (Φ.V y) ^ n).map io ≤ maximalIdeal V' ^ n := by
    intro n
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 <|
      (IsLocalRing.mem_maximalIdeal _).2 fun h => (IsLocalRing.mem_maximalIdeal _).1 hx (isUnit_of_map_unit io x h)) n
  choose S₀ hSa hSb hSc using fun κ cc => hcls κ cc j'
  set T : Finset (Fin s → Φ.X y) := C.biUnion (fun c' => Finset.univ.biUnion
    (fun i => S₀ (fun u => c' (i, u)) (c i))) with hT
  have hSfin : {mu : Fin l × Fin s → Φ.X y | mu ∈ orbit O N₁ N (k y) a ∧ ∀ i, (fun u => mu (i, u)) ∈ T}.Finite := by
    refine ((Set.Finite.pi' (fun _ : Fin l => T.finite_toSet)).image (fun x j => x j.1 j.2)).subset ?_
    intro mu hmu
    exact ⟨fun i u => mu (i, u), hmu.2, rfl⟩
  refine ⟨hSfin.toFinset, fun mu hmu => (hSfin.mem_toFinset.1 hmu).1, fun mu hmu hmuS => ?_, ?_⟩
  · rw [hSfin.mem_toFinset] at hmuS
    obtain ⟨i, hi⟩ : ∃ i, (fun u => mu (i, u)) ∉ T := by
      by_contra hcon
      push_neg at hcon
      exact hmuS ⟨hmu, hcon⟩
    obtain ⟨gm, g1, g2, g3, g4⟩ := hmu
    obtain ⟨c', hc', hcc⟩ := hC3 (fun idx => gm (a idx)) ⟨gm, g1, g2, g3, fun idx => OrbTrace.cm_refl _⟩
    have hcong : ∀ v, CongMod N (mu (i, v)) (k y (c' (i, v))) := fun v =>
      OrbTrace.cm_trans (g4 _) (OrbTrace.cm_map (k y) (OrbTrace.cm_symm (hcc _)))
    have hnot : (fun u => mu (i, u)) ∉ S₀ (fun u => c' (i, u)) (c i) := fun h =>
      hi (Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩⟩)
    have h1 := hSb (fun u => c' (i, u)) (c i) (fun u => mu (i, u)) hcong hnot
    have hnn : ∀ fi i', 0 ≤ qW W (Φ.δ y fi) (fun u => mu (i', u)) := fun fi i' =>
      qW_nonneg Φ.posW (Φ.bal y fi).1 (Φ.nonneg y fi) _
    calc (j : ℤ) ≤ j' := by exact_mod_cast hjj
      _ ≤ ∑ fi, qW W (Φ.δ y fi) (fun u => mu (i, u)) := h1
      _ ≤ ∑ fi, lin W mu (Φ.δ y fi) := Finset.sum_le_sum fun fi _ =>
          Finset.single_le_sum (f := fun i' => qW W (Φ.δ y fi) (fun u => mu (i', u))) (fun i' _ => hnn fi i')
            (Finset.mem_univ i)
  · have key : ∀ c' ∈ C, ∀ i (U : Finset (Fin s → Φ.X y)), S₀ (fun u => c' (i, u)) (c i) ⊆ U →
        (∀ ν ∈ U, ∀ v, CongMod N (ν v) (k y (c' (i, v)))) →
        ev' (f (fun u => c' (i, u)) (c i)) - io (∑ ν ∈ U, Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν) ∈
          maximalIdeal V' ^ j' := by
      intro c' hc' i U hU hU'
      rw [← Finset.sum_sdiff hU, map_add (f := _)]
      have e2 : ∀ x y z : V', x - (y + z) = (x - z) - y := fun _ _ _ => by ring
      rw [e2]
      refine sub_mem (hSc _ _) (hmap j' (Ideal.mem_map_of_mem io (Ideal.sum_mem _ fun ν hν => ?_)))
      obtain ⟨hνU, hνS⟩ := Finset.mem_sdiff.1 hν
      exact term_mem Φ y ν (c i) j' (hSb _ _ ν (hU' ν hνU) hνS)
    have hsum := OrbTrace.sum_orbit_eq C hC1 hC2 hC3 (k y) (hk y) T hSfin.toFinset (fun mu => hSfin.mem_toFinset)
      (fun i ν => Φ.u y ν (c i) * mono W (Φ.t y) (Φ.δ y) ν)
    have hF' : ev' F - io (∑ mu ∈ hSfin.toFinset, ∏ i, Φ.u y (fun v => mu (i, v)) (c i) *
        mono W (Φ.t y) (Φ.δ y) (fun v => mu (i, v))) ∈ maximalIdeal V' ^ j' := by
      rw [hsum]
      rw [← Ideal.Quotient.eq]

      rw [hF, map_sum ev', map_sum io, map_sum (Ideal.Quotient.mk _), map_sum (Ideal.Quotient.mk _)]
      refine Finset.sum_congr rfl fun c' hc' => ?_
      rw [map_prod ev', map_prod io, map_prod (Ideal.Quotient.mk _), map_prod (Ideal.Quotient.mk _)]
      refine Finset.prod_congr rfl fun i _ => Ideal.Quotient.eq.2 (key c' hc' i _ ?_ ?_)
      · intro ν hν
        exact Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨c', hc', Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hν⟩⟩,
          hSa _ _ ν hν⟩
      · intro ν hν
        exact (Finset.mem_filter.1 hν).2
    have hD : ev' F - io (Φ.ev y g₀) ∈ ((maximalIdeal A ^ e).map (Φ.ev y)).map io := by
      have h1 := Ideal.mem_map_of_mem ev' hbF
      rw [Ideal.map_map, hcomm, ← Ideal.map_map, map_mul, map_sub] at h1
      have hu : IsUnit (ev' b) := by
        by_contra h
        exact hb (by rw [← hcomap]; exact Ideal.mem_comap.2 ((IsLocalRing.mem_maximalIdeal _).2 h))
      have h2 := (Ideal.unit_mul_mem_iff_mem _ hu).1 h1
      have h3 : ev' (algebraMap A (integralClosure A L) g₀) = io (Φ.ev y g₀) := RingHom.congr_fun hcomm g₀
      rwa [h3] at h2
    rw [← hpure (maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y))]
    refine Ideal.mem_comap.2 ?_
    rw [Ideal.map_sup, map_sub]
    have h4 := sub_mem (Ideal.mem_sup_left (T := ((maximalIdeal A ^ e).map (Φ.ev y)).map io) (hJj hF'))
      (Ideal.mem_sup_right (S := (maximalIdeal (Φ.V y) ^ j).map io) hD)
    rwa [sub_sub_sub_cancel_left] at h4

end GlobalTheory.Poinc.SFour
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ValDescent

theorem spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem eq_of_comp_jK {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {f g : X ⟶ Sp (FractionRing R)}
    (h : f ≫ jK R = g ≫ jK R) : f = g := by
  haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
  exact (cancel_mono (jK R)).1 h

theorem desc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ
  have := C.semi.smooth
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  haveI : Flat C.gp := Modif.flat_gp R C.toModif
  haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance
  haveI : Flat (pullback.fst T.β C.α) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance
  set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁
  set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂
  have hq : q₁ ≫ T.β = q₂ ≫ C.α := pullback.condition
  set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ
  have hρi : Function.Injective ρ := (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd
  set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht
  have hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ := pullback.condition
  have hinj : ∀ V, Function.Injective (d.app V) := by
    intro V
    have : IsDominant (spMap ρ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)
    have : IsSchemeTheoreticallyDominant d :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip
    have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance
    exact d.app_injective V

  have hover : t ≫ jFK (R := R) F = d ≫ q₂ ≫ C.A.A.hom := by
    apply ValDescent.eq_of_comp_jK
    have e₁ : jFK (R := R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext hF
    have e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π := by
      rw [← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]
    have e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R := by
      rw [← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]
    rw [Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁,
      hq, Category.assoc, e₃]
    simp only [Category.assoc]
  let P' : Over (Sp (FractionRing R)) := Over.mk (d ≫ q₂ ≫ C.A.A.hom)
  let ℓ : P' ⟶ TFK (R := R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))
  have hfst : ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left = t := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left = d ≫ q₂ := by
    rw [← Over.comp_left, lift_snd]; rfl

  have hL : C.P.L.L.IsLB := C.P.L.isLB
  set i := J (p ≫ T.β) with hi
  set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ
  set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα
  set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV
  have l₀ : V ≤ q₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))
  let b : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) *
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))
  have ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)
  have kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _))
      ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))
  have hab : a = b := by
    apply hinj V
    refine fn_ext fun x hx => ?_
    rw [gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]
    have hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i := Set.mem_iInter.1 hx.1 0
    obtain ⟨J', hJ', eJ'⟩ := exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hmem)
    have e₁ : J' ((d ≫ q₁) ≫ T.β) = i := eJ' 0
    have e₂ : J' ((d ≫ q₂) ≫ C.α) = i := by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁
    rw [ka _ d x J' hx e₁, kb _ d x J' hx e₂]
    have h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
      rw [← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]
    have h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ρ := by
      rw [← Category.assoc, hfst, Category.assoc, hdt]
    have := H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'
    rw [hsnd] at this
    exact this

  set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu
  have hu₁ : u ≫ q₁ = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = p' := pullback.lift_snd _ _ _
  have hz : u z ∈ V := by
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [← hu₁] at h
      exact h
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [hpp, ← hu₂] at h
      exact h
  have A := ka Z u z J hz (by rw [hu₁])
  have B := kb Z u z J hz (by rw [hu₂, ← hpp])
  rw [hu₁] at A B
  rw [hu₂] at B
  rw [hab] at A
  exact A.symm.trans B

end GlobalTheory.Mum.ValDescent
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UnitGen

def gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (((Sp A).presheaf.map (homOfLE h).op).hom ((f.app V).hom c))

theorem gs_gv {A : Type} [CommRing A] {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens) (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V))
    (z : Sp A) : gs f z V c = stalkOf z (gv f V h c) := by
  rw [gs_eq f z V (h trivial)]
  simp only [stalkOf, gv, RingHom.comp_apply]
  rw [Iso.hom_inv_id_apply]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

theorem gs_spMap_top {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) (e : Γ(Sp A, ⊤)) (z : Sp B) :
    gs (spMap ψ) z ⊤ e = stalkOf z (ψ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom e)) := by
  rw [gs_eq _ z ⊤ trivial]
  simp only [stalkOf, RingHom.comp_apply]
  have := congrArg (fun q => q.hom e) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [← this, Iso.hom_inv_id_apply]
  rfl

theorem gs_comp_gv {A B : Type} [CommRing A] [CommRing B] (ψ : A →+* B) {X : Scheme.{0}} (f : Sp A ⟶ X) (V : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ V) (c : Γ(X, V)) (z : Sp B) : gs (spMap ψ ≫ f) z V c = stalkOf z (ψ (gv f V h c)) := by
  rw [← gs_pull (spMap ψ) f z V (h trivial) c, ← gs_res (spMap ψ) z h trivial, gs_spMap_top]
  rfl

theorem sp_field_eq {F : Type} [Field F] (a b : Sp F) : a = b :=
  PrimeSpectrum.ext (by haveI := a.isPrime; haveI := b.isPrime; rw [Ideal.eq_bot_of_prime a.asIdeal, Ideal.eq_bot_of_prime b.asIdeal])

end GlobalTheory.Mum.UnitGen


open GlobalTheory.Mum.UnitGen in
theorem GlobalTheory.Mum.UnitGen.value_unit_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (s : SecK C.P.L.L C.α k), ∃ x y : R, y ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (a : W) (σ : SecK C.P.L.L T.β k), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom a) * sval s p' z J) → ∀ J, Good C.P.L.L (cpt W) J → stalkOf (cpt W) (T.φ y) * sval σ (unitW T.G) (cpt W) J = stalkOf (cpt W) (a * T.φ x) * (val C.P.L.rig T.ξ (cpt W) J).val ^ k := by
  intro R _ _ _ hB D C k s
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  have hrg : C.P.L.rig.IsGen := C.P.L.rigGen
  have hE : eSec C.A.A ≫ C.α = C.gp ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback C.α_cart
  obtain ⟨i₀, hi₀⟩ := exists_chart hL ((C.gp ≫ eSec C.G) (cpt (FractionRing R)))
  have hs₀ : ⊤ ≤ (eSec C.A.A) ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hE]; exact hi₀)
  have hr₀ : ⊤ ≤ C.gp ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hi₀)
  set cs : FractionRing R := gv (eSec C.A.A) _ hs₀ (s.f (fun _ => i₀)) with hcs
  set cr : FractionRing R := gv C.gp _ hr₀ (C.P.L.rig.s (fun _ => i₀)).val with hcr
  have hcr0 : IsUnit cr := ((((C.P.L.rig.s (fun _ => i₀)).isUnit.map (C.gp.app _).hom).map _).map _)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := R) (cs / cr ^ k)
  refine ⟨x, y, nonZeroDivisors.ne_zero hy, ?_⟩
  intro W _ _ _ T a σ hσ J hJ

  have hinj : Function.Injective ((algebraMap W (FractionRing W)).comp T.φ) :=
    (IsFractionRing.injective W (FractionRing W)).comp T.inj
  obtain ⟨ga, hga, hgp⟩ := Modif.factor_gp R C.toModif (FractionRing W) ((algebraMap W _).comp T.φ) (jK W ≫ T.ξ) hinj (by
    rw [Category.assoc, T.ξ_π]
    exact (Spec.map_comp _ _).symm)
  have hjK : jK W = spMap (algebraMap W (FractionRing W)) := rfl
  have hU : unitW T.G ≫ T.β = T.ξ ≫ eSec C.G := GlobalTheory.ZJ.eSec_comp_of_isGrpPullback T.cart
  set g : Sp (FractionRing W) := cpt (FractionRing W)
  set p : Sp (FractionRing W) ⟶ T.G.left := jK W ≫ unitW T.G with hp
  set p' : Sp (FractionRing W) ⟶ C.A.A.left := spMap ga ≫ eSec C.A.A with hp'
  have hr : jK W ≫ T.ξ ≫ eSec C.G = spMap ga ≫ C.gp ≫ eSec C.G := by rw [← Category.assoc, hgp, Category.assoc]
  have hpp : p ≫ T.β = p' ≫ C.α := by
    rw [hp, hp', Category.assoc, Category.assoc, hU, hE, hr]
  set I := J (T.ξ ≫ eSec C.G) with hIdef
  have hI : (T.ξ ≫ eSec C.G) (cpt W) ∈ C.P.L.L.U I := hJ _
  have hItop : ⊤ ≤ (T.ξ ≫ eSec C.G) ⁻¹ᵁ C.P.L.L.U I := (top_le_iff_cpt _ _).2 hI
  have hpI : (p ≫ T.β) g ∈ C.P.L.L.U I := by
    rw [hp, Category.assoc, hU, Scheme.Hom.comp_apply]; exact hItop trivial
  have hpi₀ : (p ≫ T.β) g ∈ C.P.L.L.U i₀ := by
    rw [hp, Category.assoc, hU, ← Category.assoc, hgp, Category.assoc, Scheme.Hom.comp_apply,
      sp_field_eq ((spMap ga) g) (cpt (FractionRing R))]
    exact hi₀
  obtain ⟨J', hJ', hJ'e⟩ := exists_good C.P.L.L hL g (K := PUnit) (fun _ => p ≫ T.β) (fun _ => I) (fun _ _ _ => rfl)
    (fun _ => hpI)
  have e1 := hσ _ p p' hpp g J' hJ'
  rw [sval_of σ p g J' (fun _ => I) (fun _ => hJ'e ⟨⟩),
    sval_of s p' g J' (fun _ => I) (fun _ => by rw [← hpp]; exact hJ'e ⟨⟩)] at e1

  have hσtop : ⊤ ≤ unitW T.G ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hU]; exact hI)
  have hρtop : ⊤ ≤ T.ξ ⁻¹ᵁ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) :=
    (top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun _ => by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]; exact hI)
  set σv : W := gv (unitW T.G) _ hσtop (σ.f (fun _ => I)) with hσv
  set ρv : W := gv T.ξ _ hρtop (C.P.L.rig.s (fun _ => I)).val with hρv
  have eσ : gs p g (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf g (algebraMap W _ σv) := by
    rw [hp, hjK]; exact gs_comp_gv _ _ _ hσtop _ g
  have hu : unitW T.G ≫ T.G.hom = 𝟙 _ := by simpa [unitW, eSec] using Over.w (η[T.G])
  have ea : gs p g ⊤ (scal T.G.hom a) = stalkOf g (algebraMap W _ a) := by
    have h1 : p ≫ T.G.hom = spMap (algebraMap W (FractionRing W)) := by
      rw [hp, Category.assoc, hu, Category.comp_id]
    have h2 := gs_pull p T.G.hom g ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom a)
    rw [h1, gs_spMap_top, Iso.inv_hom_id_apply] at h2
    exact h2

  have hrp : (jK W ≫ T.ξ) ≫ eSec C.G = p ≫ T.β := by rw [hp, Category.assoc, Category.assoc, hU]
  have hp'i₀ : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpi₀
  have hp'I : p' g ∈ LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hpp]; exact hpI
  have hri₀ : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpi₀
  have hrI : (jK W ≫ T.ξ) g ∈ LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I) := Set.mem_iInter.2 fun _ => by
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, hrp]; exact hpI
  have e2 := sec_trans s p' g hp'i₀ hp'I
  have orbitMap_conj_smul_zero : gs p' g (LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i₀)) (s.f (fun _ => i₀)) = stalkOf g (ga cs) := by
    rw [hp']; exact gs_comp_gv ga _ _ hs₀ _ g
  have e3 := gen_trans hrg (jK W ≫ T.ξ) g hri₀ hrI
  have eB0 : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => i₀)) (C.P.L.rig.s (fun _ => i₀))).val = stalkOf g (ga cr) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hri₀ _).symm.trans ?_
    rw [hgp]; exact gs_comp_gv ga _ _ hr₀ _ g
  have eB : (gm (jK W ≫ T.ξ) g (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf g (algebraMap W _ ρv) := by
    refine (gs_unit (jK W ≫ T.ξ) g _ hrI _).symm.trans ?_
    rw [hjK]; exact gs_comp_gv _ _ _ hρtop _ g
  have et : trF (L := C.P.L.L) (fun _ : Fin 1 => C.α) (fun _ => ((k : ℕ) : ℤ)) p' g (fun _ => i₀) (fun _ => I) =
      (trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀) (fun _ => I)) ^ k := by
    simp only [trF]
    rw [show p' ≫ C.α = (jK W ≫ T.ξ) ≫ eSec C.G from hpp.symm.trans hrp.symm]
    simp

  rw [eσ, ea] at e1
  rw [orbitMap_conj_smul_zero, et] at e2
  have e3v := congrArg Units.val e3
  rw [Units.val_mul, eB0, eB] at e3v
  have hy0 : algebraMap R (FractionRing R) y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hxy' : algebraMap R _ x * cr ^ k = cs * algebraMap R _ y := by
    rw [div_eq_div_iff hy0 (pow_ne_zero _ hcr0.ne_zero)] at hxy; exact hxy
  have hXY := congrArg (fun q => stalkOf g (ga q)) hxy'
  simp only [map_mul, map_pow, hga, RingHom.comp_apply] at hXY
  rw [e3v, e2, Units.val_pow_eq_pow_val] at hXY
  have hW : T.φ y * σv = a * T.φ x * ρv ^ k := by
    apply ((stalkOf_injective g).comp (IsFractionRing.injective W (FractionRing W)))
    simp only [Function.comp_apply, map_mul, map_pow]
    refine ((trF (L := C.P.L.L) (fun _ : PUnit => eSec C.G) (fun _ => 1) (jK W ≫ T.ξ) g (fun _ => i₀)
      (fun _ => I)).isUnit.pow k).mul_left_inj.1 ?_
    rw [e1]
    linear_combination (-(stalkOf g (algebraMap W (FractionRing W) a))) * hXY
  have eBc : (gm T.ξ (cpt W) (LB.wchart C.P.L.L (fun _ : PUnit => eSec C.G) (fun _ => I)) (C.P.L.rig.s (fun _ => I))).val = stalkOf (cpt W) ρv :=
    (gs_unit T.ξ (cpt W) _ (hρtop trivial) _).symm.trans (gs_gv _ _ hρtop _ _)
  have eσc : gs (unitW T.G) (cpt W) (LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => I)) (σ.f (fun _ => I)) =
      stalkOf (cpt W) σv := gs_gv _ _ hσtop _ _
  rw [sval_of σ (unitW T.G) (cpt W) J (fun _ => I) (fun _ => by rw [hU])]
  erw [eσc]
  rw [val_of C.P.L.rig T.ξ (cpt W) J (fun _ => I) (fun _ => rfl), eBc, ← map_mul, ← map_pow, ← map_mul, hW]
end
end
