module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerTowerQqPowLevelEqQ
public import Formalism.FockGram.StatementFock
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Basic.Complex.Basic
public import Formalism.FormalDegreeBessel.StatementG
public import Formalism.PairingDivisors.StatementN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle039
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem kaehler_rel_isInt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (n : ℕ) (ι : On p n →ₐ[O0 p] Ω) (S : Subalgebra (O0 p) Ω)
    (hS : ∀ x ∈ S, IsInt (p := p) x)
    (hι : ∀ x, ι x ∈ S) (D : Ω → Ω) (hD : GlobalTheory.KumDlog.IsDer S D) (a b c x y z : On p n)
    (hrel : a • KaehlerDifferential.D (O0 p) (On p n) x =
      b • KaehlerDifferential.D (O0 p) (On p n) y + c • KaehlerDifferential.D (O0 p) (On p n) z) :
    IsInt (p := p) (ι a * D (ι x) - ι b * D (ι y) - ι c * D (ι z)) := by
  letI : Module (On p n) Ω := Module.compHom Ω ι.toRingHom
  have hsm : ∀ (r : On p n) (w : Ω), r • w = ι r * w := fun _ _ => rfl
  haveI : IsScalarTower (O0 p) (On p n) Ω := ⟨fun r s w => by
    rw [hsm, hsm, map_smul, smul_mul_assoc]⟩
  let N : Submodule (On p n) Ω :=
    { carrier := {w | IsInt (p := p) w}
      add_mem' := fun ha hb => int_add ha hb
      zero_mem' := int_zero
      smul_mem' := fun r w hw => by
        show IsInt (p := p) (r • w)
        rw [hsm]; exact int_mul (hS _ (hι r)) hw }
  have memN : ∀ w, w ∈ N ↔ IsInt (p := p) w := fun _ => Iff.rfl
  have key : ∀ w w' : Ω, IsInt (p := p) (w - w') → N.mkQ w = N.mkQ w' := fun w w' h =>
    (Submodule.Quotient.eq N).2 h
  let L : On p n →ₗ[O0 p] Ω ⧸ N :=
    { toFun := fun u => N.mkQ (D (ι u))
      map_add' := fun u v => by
        rw [← map_add (f := _)]
        refine key _ _ ?_
        rw [map_add (f := _)]
        exact int_congr (hD.1 _ (hι u) _ (hι v)) (by ring)
      map_smul' := fun r u => by
        simp only [RingHom.id_apply]
        rw [← LinearMap.map_smul_of_tower]
        refine key _ _ ?_
        rw [map_smul, Algebra.smul_def, Algebra.smul_def]
        exact hD.alg_mul hS r (hι u) }
  let d : Derivation (O0 p) (On p n) (Ω ⧸ N) := Derivation.mk' L (fun u v => by
    show N.mkQ (D (ι (u * v))) = u • N.mkQ (D (ι v)) + v • N.mkQ (D (ι u))
    rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _)]
    refine key _ _ ?_
    rw [hsm, hsm, map_mul]
    exact int_congr (hD.2.1 _ (hι u) _ (hι v)) (by ring))
  have hd : ∀ u, d.liftKaehlerDifferential (KaehlerDifferential.D (O0 p) (On p n) u) =
      N.mkQ (D (ι u)) := fun u => by
    rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
  have h2 := congrArg d.liftKaehlerDifferential hrel
  simp only [map_add (f := _), LinearMap.map_smul, hd] at h2
  rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add (f := _),
    ← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, N.ker_mkQ, memN, hsm, hsm, hsm] at h2
  exact int_congr h2 (by ring)

end GlobalTheory.KumDlog
end
end

section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.KumDlog

theorem der_dual_p_sq_int : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω],
    ∀ (B C : Subalgebra (O0 p) Ω) (ι : Type) [Fintype ι] (u v : ι → Ω) (tr : Ω → Ω),
    DualData B C u v tr →
  ∀ D : Ω → Ω, IsDer C D → ∀ x ∈ C, (∀ k l, IsInt (p := p) (D (tr (u l * (x * v k))))) →
    IsInt (p := p) ((p : Ω) ^ 2 * D x) := by
  intro p _ Ω _ _ B C ι _ u v tr hd D hD x hx hT
  obtain ⟨hBC, hCi, hu, hv, htr, -, -, hsu, hsv, huv⟩ := hd
  have s1 : ∀ k, IsInt (p := p) ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l)) := by
    intro k
    have hy : x * v k ∈ C := mul_mem hx (hv k)
    have a1 := hD.alg_mul hCi (p : O0 p) hy
    simp only [map_natCast] at a1
    rw [← hsv _ hy] at a1
    have a2 := hD.sum Finset.univ (fun l => v l * tr (u l * (x * v k)))
      (fun l _ => mul_mem (hv l) (hBC (htr _ (mul_mem (hu l) hy))))
    have a3 : IsInt (p := p) (∑ l, D (v l * tr (u l * (x * v k))) -
        ∑ l, tr (u l * (x * v k)) * D (v l)) := by
      rw [← Finset.sum_sub_distrib]
      refine int_sum _ _ fun l _ => ?_
      have ht : tr (u l * (x * v k)) ∈ C := hBC (htr _ (mul_mem (hu l) hy))
      exact int_congr (int_add (hD.2.1 _ (hv l) _ ht) (int_mul (hCi _ (hv l)) (hT k l))) (by ring)
    exact int_congr (int_add (int_add (int_neg a1) a2) a3) (by ring)
  have e2 : ∀ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) = (p : Ω) * (x * (u l * D (v l))) := by
    intro l
    have h := hsu (x * u l) (mul_mem hx (hu l))
    calc ∑ k, u k * (tr (u l * (x * v k)) * D (v l))
        = (∑ k, u k * tr (v k * (x * u l))) * D (v l) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show u l * (x * v k) = v k * (x * u l) by ring]; ring
      _ = _ := by rw [h]; ring
  have e : ∑ k, u k * ∑ l, tr (u l * (x * v k)) * D (v l) = (p : Ω) * (x * ∑ l, u l * D (v l)) := by
    calc _ = ∑ l, ∑ k, u k * (tr (u l * (x * v k)) * D (v l)) := by
            simp_rw [Finset.mul_sum]; exact Finset.sum_comm
      _ = ∑ l, (p : Ω) * (x * (u l * D (v l))) := Finset.sum_congr rfl fun l _ => e2 l
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
  have s2 : IsInt (p := p) ((p : Ω) * ∑ k, u k * D (x * v k) - (p : Ω) * (x * ∑ l, u l * D (v l))) := by
    have a : IsInt (p := p) (∑ k, u k * ((p : Ω) * D (x * v k) - ∑ l, tr (u l * (x * v k)) * D (v l))) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (s1 k)
    refine int_congr a ?_
    rw [← e, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : IsInt (p := p) (∑ k, u k * D (x * v k) - x * ∑ k, u k * D (v k) - (p : Ω) * D x) := by
    have a : IsInt (p := p) (∑ k, u k * (D (x * v k) - x * D (v k) - v k * D x)) :=
      int_sum _ _ fun k _ => int_mul (hCi _ (hu k)) (hD.2.1 x hx (v k) (hv k))
    refine int_congr a ?_
    rw [← huv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact int_congr (int_sub s2 (int_mul (int_nat p) s3)) (by ring)

end GlobalTheory.KumDlog
end

section

noncomputable section

open GlobalTheory.K5 GlobalTheory.KumDlog

namespace GlobalTheory.TraceTower

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem eq_on_fix {T : Tower p Ω} {r : Ω} {h h' : Gal p Ω} (hh : h ∈ Hinf T) (hh' : h' ∈ Hinf T)
    (e : h r = h' r) {x : Ω} (hx : x ∈ FixI (Hfix T r)) : h x = h' x := by
  have hm : h'⁻¹ * h ∈ Hfix T r := by
    refine ⟨(Hinf T).mul_mem ((Hinf T).inv_mem hh') hh, ?_⟩
    refine MulAction.mem_stabilizer_iff.2 ?_
    rw [AlgEquiv.smul_def, AlgEquiv.mul_apply, e]
    exact h'.symm_apply_apply r
  have h1 : h'.symm (h x) = x := hx.2 _ hm
  exact h'.symm_apply_eq.1 h1

end GlobalTheory.TraceTower

open GlobalTheory.TraceTower in
theorem GlobalTheory.traceTower_dualData : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∀ (ι : Type) [Fintype ι] (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) → (∀ k, v k ∈ FixI (Hfix T r)) →
  ∑ k, u k * v k = (p : Ω) → (∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0) →
  ∃ tr : Ω → Ω, DualData (FixI (Hinf T)) (FixI (Hfix T r)) u v tr := by
  intro p _ Ω _ _ T n r _ hor ι _ u v hu hv huv hz
  classical
  have hfin : {ρ : Ω | ∃ h ∈ Hinf T, h r = ρ}.Finite := by
    refine ((Finset.range (p ^ n)).image (fun i => T.ζ n ^ i * r)).finite_toSet.subset ?_
    rintro ρ ⟨h, hh, rfl⟩
    obtain ⟨i, hi⟩ := hor h hh
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    refine ⟨i % p ^ n, Nat.mod_lt _ (ppow_pos n), ?_⟩
    rw [hi]
    congr 1
    conv_rhs => rw [← Nat.div_add_mod i (p ^ n)]
    rw [pow_add, pow_mul, (T.prim n).pow_eq_one, one_pow, one_mul]
  set O := hfin.toFinset with hOdef
  have hO : ∀ ρ, ρ ∈ O ↔ ∃ h ∈ Hinf T, h r = ρ := fun ρ => hfin.mem_toFinset
  have hg0 : ∀ ρ, ∃ f : Gal p Ω, ρ ∈ O → f ∈ Hinf T ∧ f r = ρ := by
    intro ρ
    by_cases hρ : ρ ∈ O
    · obtain ⟨h, hh, e⟩ := (hO ρ).1 hρ
      exact ⟨h, fun _ => ⟨hh, e⟩⟩
    · exact ⟨1, fun h => absurd h hρ⟩
  choose g hg using hg0
  have hrO : r ∈ O := (hO r).2 ⟨1, (Hinf T).one_mem, rfl⟩
  have fixr : ∀ x ∈ FixI (Hfix T r), g r x = x := fun x hx =>
    hx.2 _ ⟨(hg r hrO).1, MulAction.mem_stabilizer_iff.2 (by rw [AlgEquiv.smul_def]; exact (hg r hrO).2)⟩
  have kk : ∀ f ∈ Hinf T, ∀ ρ ∈ O, ∀ x ∈ FixI (Hfix T r), f (g ρ x) = g (f ρ) x ∧ f ρ ∈ O := by
    intro f hf ρ hρ x hx
    have hm : f * g ρ ∈ Hinf T := (Hinf T).mul_mem hf (hg ρ hρ).1
    have hr' : (f * g ρ) r = f ρ := by rw [AlgEquiv.mul_apply, (hg ρ hρ).2]
    have hfO : f ρ ∈ O := (hO _).2 ⟨_, hm, hr'⟩
    refine ⟨?_, hfO⟩
    have := eq_on_fix hm (hg _ hfO).1 (by rw [hr', (hg _ hfO).2]) hx
    rwa [AlgEquiv.mul_apply] at this
  have zero_inv : ∀ ρ ∈ O, ρ ≠ r → ∑ k, v k * g ρ (u k) = 0 := by
    intro ρ hρ hne
    set f := g ρ
    have hf : f ∈ Hinf T := (hg ρ hρ).1
    have hne' : f⁻¹ r ≠ r := by
      intro e
      apply hne
      rw [← (hg ρ hρ).2]
      have e' : f.symm r = r := e
      conv_lhs => rw [← e']
      exact f.apply_symm_apply r
    have h0 := hz _ ((Hinf T).inv_mem hf) hne'
    calc ∑ k, v k * f (u k) = f (∑ k, u k * f⁻¹ (v k)) := by

          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
          have : f (f⁻¹ (v k)) = v k := f.apply_symm_apply (v k)
          rw [this, mul_comm]
      _ = 0 := by rw [h0, map_zero]
  refine ⟨fun x => ∑ ρ ∈ O, g ρ x, fun x hx => ⟨hx.1, fun f hf => hx.2 f hf.1⟩, fun x hx => hx.1,
    hu, hv, ?_, ?_, ?_, ?_, ?_, huv⟩
  · intro x hx
    refine ⟨int_sum _ _ fun ρ _ => int_gal _ hx.1, fun f hf => ?_⟩
    show f (∑ ρ ∈ O, g ρ x) = ∑ ρ ∈ O, g ρ x

    rw [map_sum]
    calc ∑ ρ ∈ O, f (g ρ x) = ∑ ρ ∈ O, g (f ρ) x :=
          Finset.sum_congr rfl fun ρ hρ => (kk f hf ρ hρ x hx).1
      _ = ∑ ρ ∈ O, g ρ x := by
        refine Finset.sum_nbij' (fun ρ => f ρ) (fun ρ => f.symm ρ) (fun ρ hρ => (kk f hf ρ hρ x hx).2)
          (fun ρ hρ => (kk f⁻¹ ((Hinf T).inv_mem hf) ρ hρ x hx).2) (fun ρ _ => f.symm_apply_apply ρ)
          (fun ρ _ => f.apply_symm_apply ρ) (fun ρ _ => rfl)
  · intro x _ y _
    simp only [map_add (f := _), Finset.sum_add_distrib]
  · intro b hb x _
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [map_mul, hb.2 _ (hg ρ hρ).1]
  · intro y hy
    calc ∑ k, u k * ∑ ρ ∈ O, g ρ (v k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, u k * g ρ (v k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, u k * g r (v k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [hz _ (hg ρ hρ).1 (by rw [(hg ρ hρ).2]; exact hne), mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (v k) (hv k)], huv, mul_comm]
  · intro y hy
    calc ∑ k, v k * ∑ ρ ∈ O, g ρ (u k * y) = ∑ ρ ∈ O, g ρ y * ∑ k, v k * g ρ (u k) := by
          simp only [map_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun k _ => by ring
      _ = g r y * ∑ k, v k * g r (u k) := by
          refine Finset.sum_eq_single r (fun ρ hρ hne => ?_) (fun h => absurd hrO h)
          rw [zero_inv ρ hρ hne, mul_zero]
      _ = p * y := by
          rw [fixr y hy, Finset.sum_congr rfl fun k _ => by rw [fixr (u k) (hu k)], ← huv,
            mul_comm]
          congr 1
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end
end

section

noncomputable section

namespace GlobalTheory.JointHarm

open MvPolynomial Matrix

section Minors

variable {R : Type*} [CommRing R]

variable {n l : ℕ}

end Minors

variable {n p q : ℕ}

section Killed

end Killed

section Fock

open Formalism.E

theorem fock_add_left {σ : Type} (P P' Q : MvPolynomial σ ℂ) :
    fock (P + P') Q = fock P Q + fock P' Q := by
  classical
  have key : ∀ (F : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)), F.support ⊆ s →
      fock F Q = ∑ m ∈ s, F.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by
    intro F s hs
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [notMem_support_iff.mp hm, zero_mul, zero_mul]
  rw [key _ _ support_add, key P _ Finset.subset_union_left, key P' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]; ring

theorem fock_monomial_left {σ : Type} (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    fock (monomial α c) Q = c * star (Q.coeff α) * (Formalism.A.mfact α : ℂ) := by
  classical
  unfold fock
  rw [support_monomial]
  split_ifs with hc
  · simp [hc]
  · simp

variable {σ₁ σ₂ τ : Type} {f : σ₁ → τ} {g : σ₂ → τ}

theorem mapDomain_add_inj (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) {α α' : σ₁ →₀ ℕ} {β β' : σ₂ →₀ ℕ}
    (h : α.mapDomain f + β.mapDomain g = α'.mapDomain f + β'.mapDomain g) : α = α' ∧ β = β' := by
  constructor
  · ext x
    have := DFunLike.congr_fun h (f x)
    have hx : f x ∉ Set.range g := fun ⟨y, hy⟩ => hfg x y hy.symm
    simpa [Finsupp.mapDomain_apply_of_injective hf, Finsupp.mapDomain_notin_range _ _ hx] using this
  · ext y
    have := DFunLike.congr_fun h (g y)
    have hy : g y ∉ Set.range f := fun ⟨x, hx⟩ => hfg x y hx
    simpa [Finsupp.mapDomain_apply_of_injective hg, Finsupp.mapDomain_notin_range _ _ hy] using this

theorem coeff_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) (P : MvPolynomial σ₁ ℂ)
    (Q : MvPolynomial σ₂ ℂ) :
    AddMonoidAlgebra.coeff (rename f P * rename g Q) (α.mapDomain f + β.mapDomain g) = AddMonoidAlgebra.coeff P α * AddMonoidAlgebra.coeff Q β := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [map_add (f := _), add_mul, MvPolynomial.coeff_add, h, h']
  | monomial α' x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add (f := _), mul_add, MvPolynomial.coeff_add, h, h']
    | monomial β' y =>
      rw [rename_monomial, rename_monomial, monomial_mul, coeff_monomial, coeff_monomial,
        coeff_monomial]
      by_cases h : α'.mapDomain f + β'.mapDomain g = α.mapDomain f + β.mapDomain g
      · obtain ⟨rfl, rfl⟩ := mapDomain_add_inj hf hg hfg h
        simp
      · rw [if_neg h]
        split_ifs with h1 h2
        · exact absurd (by rw [h1, h2]) h
        all_goals simp

theorem mfact_mapDomain_add (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (α : σ₁ →₀ ℕ) (β : σ₂ →₀ ℕ) :
    Formalism.A.mfact (α.mapDomain f + β.mapDomain g) = Formalism.A.mfact α * Formalism.A.mfact β := by
  classical
  unfold Formalism.A.mfact
  rw [Finsupp.prod_add_index_of_disjoint, Finsupp.prod_mapDomain_index_inj hf,
    Finsupp.prod_mapDomain_index_inj hg]
  rw [Finsupp.mapDomain_support_of_injective hf, Finsupp.mapDomain_support_of_injective hg,
    Finset.disjoint_left]
  intro t h1 h2
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h2
  exact hfg x y hy.symm

theorem fock_rename_mul (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ x y, f x ≠ g y) (P P' : MvPolynomial σ₁ ℂ) (Q Q' : MvPolynomial σ₂ ℂ) :
    fock (rename f P * rename g Q) (rename f P' * rename g Q') = fock P P' * fock Q Q' := by
  induction P using MvPolynomial.induction_on' with
  | add P₁ P₂ h h' => simp only [map_add (f := _), add_mul, fock_add_left, h, h']
  | monomial α x =>
    induction Q using MvPolynomial.induction_on' with
    | add Q₁ Q₂ h h' => simp only [map_add (f := _), mul_add, fock_add_left, h, h']
    | monomial β y =>
      rw [rename_monomial, rename_monomial, monomial_mul, fock_monomial_left, fock_monomial_left,
        fock_monomial_left, coeff_rename_mul hf hg hfg, mfact_mapDomain_add hf hg hfg, star_mul']
      push_cast
      ring

end Fock

end GlobalTheory.JointHarm
end
end

section

open Matrix MeasureTheory Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.BesselUnitary

def partner (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

lemma gram_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = partner k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk partner
  split_ifs <;> simp only [Fin.ext_iff] at * <;> first | rfl | omega

lemma gram_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner k r i)]
  · rw [gram_apply, gram_apply, Matrix.one_apply, if_pos rfl]
    unfold partner
    split_ifs <;> simp only [Fin.ext_iff] at * <;> first | omega | (simp; done) | (split_ifs <;> first | omega | simp)
  · intro b _ hb
    rw [gram_apply k r i b, if_neg hb, zero_mul]
  · simp

end GlobalTheory.BesselUnitary

namespace GlobalTheory

open BesselUnitary

end GlobalTheory
end
end

section


theorem _root_.GlobalTheory.T.cmValues_exponent_log_sum_le : Formalism.PairingDivisionLocalBalance.CESum := by
  first | exact @GlobalTheory.dividedPowerValuations_cESum | exact GlobalTheory.dividedPowerValuations_cESum | (intros; apply GlobalTheory.dividedPowerValuations_cESum <;> assumption)
end

section

open scoped NNReal
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem norm_uniformiser_eq_inv_absNorm :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ϖ : v.adicCompletion F),
      Formalism.UG.IsUnifV F v ϖ → ‖ϖ‖₊ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
  intro F _ _ v ϖ h
  apply NNReal.eq
  rw [coe_nnnorm, FinitePlace.norm_def]
  unfold Formalism.UG.IsUnifV at h
  rw [h]
  have hne : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [WithZeroMulInt.toNNReal_neg_apply _ hne]
  simp only [WithZero.log, WithZero.recZeroCoe_coe, toAdd_ofAdd, zpow_neg, zpow_one, NNReal.coe_inv]

end GlobalTheory
end
