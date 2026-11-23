module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem unit_eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : kˣ) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  apply Units.ext
  have h' : ((x : k) - 1) ^ l ^ m = 0 := by
    rw [sub_pow_char_pow, one_pow, ← Units.val_pow_eq_pow_val, h, Units.val_one, sub_self]
  exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero)).mp h')

private theorem mu_pow {l : ℕ} [Fact l.Prime] (F : GFrame l) (v : F.Vl) (g : F.mu v) :
    ∃ m : ℕ, (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := by
  have hg : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ∈
      CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l := g.2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ^ l ^ m = 1 := by
    first
      | exact hg
      | (obtain ⟨m, hm⟩ := hg; exact ⟨m, by rw [← hm]; exact pow_orderOf_eq_one _⟩)
  refine ⟨m, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
  exact hm

theorem UpperTheory.V.W.residualDatum_inertia_characters_trivial :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v), r.psib v i g = 1 ∧ Units.map (residue O : O →* ResidueField O) (r.th v i g) = 1 := by
  intro l _ F O _ _ _ _ n r v i g
  obtain ⟨m, hm⟩ := mu_pow F v g
  constructor
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow]
    have hle : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
      Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
        (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
    exact hle hm
  · apply unit_eq_one_of_pow l _ m
    rw [← map_pow, ← map_pow, r.th_comm v i (g ^ l ^ m) (by simpa using hm), map_one]
end

section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

section SlopeTestRemainingChoices

open Polynomial

variable {n : ℕ} {A A' A'' G : Type} [CommRing A] [CommRing A'] [CommRing A''] [Group G]

private theorem pm_map_map (D : GDet n A G) (f : A →+* A') (g : A' →+* A'') :
    (D.map f).map g = D.map (g.comp f) := rfl

private theorem pm_chi_map (D : GDet n A G) (f : A →+* A') (y : MonoidAlgebra A G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
  letI : Algebra A A'[X] := ((algebraMap A' A'[X]).comp f).toAlgebra
  have h := D.nat A[X] A'[X]
    { (Polynomial.mapRingHom f : A[X] →+* A'[X]) with
      commutes' := fun a => by
        show Polynomial.map f (C a) = C (f a)
        simp }
    (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
  refine Eq.trans ?_ h
  show D.D A'[X] _ = D.D A'[X] (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · clear h
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp

private theorem pm_lam_map (D : GDet n A G) (f : A →+* A') (i : ℕ) (y : MonoidAlgebra A G) :
    (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
  simp [GDet.lam, pm_chi_map]

private theorem pm_lam_single (D : GDet n A G) (f : A →+* A') (i : ℕ) (g : G) :
    (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  rw [← pm_lam_map]; simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.W.exists_determinantPair_map_of_algHom :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (p : Pair r R), ∃ p' : Pair r R', p.Maps (f : R →+* R') p'.D p'.ψ := by
  intro l _ F O _ _ _ n r R _ _ _ R' _ _ _ f p
  have hle : ∀ N, maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := fun N => by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  have heps : ∀ g, Units.map ((f : R →+* R') : R →* R') (F.eps O R g) = F.eps O R' g := fun g =>
    Units.ext (f.commutes _)
  refine ⟨
    { D := p.D.map (f : R →+* R')
      ψ := fun v i => pushCh (f : R →+* R') (p.ψ v i)
      cont := fun i N => ?_
      red := ?_
      psi := fun v i =>
        { cont := fun N => ((p.psi v i).cont N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
          red := fun g => (res_map f _).trans ((p.psi v i).red g)
          mu := fun g => (congrArg f ((p.psi v i).mu g)).trans (f.commutes _) }
      P := fun i g => ?_
      Ord := fun v g h => ?_
      I := fun u g hg h => ?_ }, rfl, fun _ _ => rfl⟩
  · simp only [pm_lam_single]
    exact (p.cont i N).comp (Ideal.quotientMap _ (f : R →+* R') (hle N))
  · rw [pm_map_map, ← p.red]
    congr 1
    exact RingHom.ext (res_map f)
  · have h1 : F.star O R' n (MonoidAlgebra.single g 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (F.star O R n (MonoidAlgebra.single g 1)) := by
      simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, one_smul, MonoidHom.coe_mk, OneHom.coe_mk,
        MulOpposite.unop_op, MonoidAlgebra.mapRingHom_single]
      rw [← heps, ← map_zpow]
      rfl
    rw [h1, pm_lam_map, p.P, pm_lam_single]
  · have h1 : MonoidAlgebra.single h 1 * F.oEl v (fun i => pushCh (f : R →+* R') (p.ψ v i)) g =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * F.oEl v (p.ψ v) g) := by
      simp only [GFrame.oEl, map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
        MonoidAlgebra.mapRingHom_single, map_one]
      rfl
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.Ord v g h)).trans (map_zero _)
  · have h1 : MonoidAlgebra.single h (1 : R') * (MonoidAlgebra.single g 1 - 1) =
        MonoidAlgebra.mapRingHom _ (f : R →+* R') (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) := by
      simp only [map_mul, map_sub, MonoidAlgebra.mapRingHom_single, map_one]
    rw [h1, GDet.tr, pm_lam_map]
    exact (congrArg (f : R →+* R') (p.I u g hg h)).trans (map_zero _)
end

section

noncomputable section

open IsLocalRing UpperTheory.V.Alg

namespace UpperTheory.V.W

def muG (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Subgroup G :=
  (CommGroup.primaryComponent (TopologicalAbelianization G) l).comap (QuotientGroup.mk' _)

structure LocAb (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (I : Subgroup G)
    (d : ℕ) where
  a : G →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l])
  cont : Continuous a
  surj : Function.Surjective a
  inertia : ∀ x : (Fin d → ℤ_[l]) × ℤ_[l], (∃ g ∈ I, a g = Multiplicative.ofAdd x) ↔ x.2 = 0
  univ : ∀ (C : Type) [CommGroup C] [Finite C], IsPGroup l C → ∀ χ : G →* C, IsOpen (χ.ker : Set G) →
    muG l G ≤ χ.ker → a.ker ≤ χ.ker
  b : G →* CommGroup.primaryComponent (TopologicalAbelianization G) l
  b_open : IsOpen (b.ker : Set G)
  b_mu : ∀ g ∈ muG l G, (b g : TopologicalAbelianization G) = QuotientGroup.mk' _ g

structure DetObj (O : Type) [CommRing O] [IsLocalRing O] {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (Dbar : GDet n (ResidueField O) G) : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]
  D : GDet n R G
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = Dbar
  univ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (D' : GDet n R' G), D'.IsCont (maximalIdeal R') →
    D'.map (res O R' : R' →+* ResidueField O) = Dbar → ∃! f : R →ₐ[O] R', D.map (f : R →+* R') = D'

attribute [instance] DetObj.ring DetObj.alg DetObj.co

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  (r : Resid F O n)

structure LamTObj : Type 1 where
  Λ : Type
  [ring : CommRing Λ]
  [alg : Algebra O Λ]
  [co : IsCO O Λ]
  ψ : ∀ v, Fin n → F.Gv v →* Λˣ
  psi : ∀ v i, r.IsPsi v i (ψ v i)
  univ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ψ' : ∀ v, Fin n → F.Gv v →* Rˣ),
    (∀ v i, r.IsPsi v i (ψ' v i)) → ∃! f : Λ →ₐ[O] R, ∀ v i, pushCh (f : Λ →+* R) (ψ v i) = ψ' v i

attribute [instance] LamTObj.ring LamTObj.alg LamTObj.co

def Resid.Ok : Prop :=
  (∀ v (g : Fin n → F.Gv v) (h : F.G₀), r.Dbar.tr (MonoidAlgebra.single h 1 * F.oEl v (r.psib v) g) = 0) ∧
    ∀ v i (g : F.mu v), r.psib v i g = Units.map (residue O : O →* ResidueField O) (r.th v i g)

structure FHom (F' F : GFrame l) where
  π : F'.Γ →* F.Γ
  π_cont : Continuous π
  hη : ∀ g, F.η (π g) = F'.η g
  hc : π F'.c = F.c
  hε : ∀ g, F.ε (π g) = F'.ε g
  vl : F'.Vl → F.Vl
  gv : ∀ v, F'.Gv v →* F.Gv (vl v)
  gv_cont : ∀ v, Continuous (gv v)
  hφ : ∀ v g, (F.φ (vl v) (gv v g) : F.Γ) = π (F'.φ v g)
  hI : ∀ v, ∀ g ∈ F'.Iv v, gv v g ∈ F.Iv (vl v)

namespace FHom

variable {F' : GFrame l} (h : FHom F' F)

def π₀ : F'.G₀ →* F.G₀ :=
  (h.π.comp F'.η.ker.subtype).codRestrict _ fun g => (h.hη g).trans g.2

structure Compat (r' : Resid F' O n) (r : Resid F O n) : Prop where
  chib : ∀ i, r'.chib i = (r.chib i).comp h.π₀
  psib : ∀ v i, r'.psib v i = (r.psib (h.vl v) i).comp (h.gv v)
  th : ∀ v i (g : F'.mu v) (hg : h.gv v g ∈ F.mu (h.vl v)), r'.th v i g = r.th (h.vl v) i ⟨_, hg⟩
  ip : ∀ u, ∀ g ∈ r'.Ip u, h.π₀ g = 1 ∨ ∃ u', h.π₀ g ∈ r.Ip u'

end FHom

end UpperTheory.V.W
end
end
