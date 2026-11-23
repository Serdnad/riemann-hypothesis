module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle105
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle062
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChange
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle030
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle021
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.OriginEps

open AlgebraicGeometry CategoryTheory

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem mem_adjoin_rat_of_regular {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x)
    {c : κ} (hc : x c ≠ 0) {f : Ω}
    (hf : ∀ p : Cpt ξ, InChart ξ x c p → (∀ r : ℕ, r.Prime → ¬ InFibre ξ r p) → f ∈ regAt ξ p) :
    f ∈ Algebra.adjoin ℚ (Set.range fun j => x j / x c) := by
  classical
  set B := Algebra.adjoin ℚ (Set.range fun j => x j / x c) with hB
  have hle : ∀ a ∈ chartRing ℤ x c, a ∈ B := by
    intro a ha
    have h2 : chartRing ℤ x c ≤ B.restrictScalars ℤ := Algebra.adjoin_le Algebra.subset_adjoin
    exact h2 ha
  let I : Ideal (chartRing ℤ x c) :=
    { carrier := {a | (a : Ω) * f ∈ B}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : chartRing ℤ x c) : Ω) * f ∈ B
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : chartRing ℤ x c) : Ω) * f ∈ B
        simp
      smul_mem' := fun a u hu => by
        show ((a • u : chartRing ℤ x c) : Ω) * f ∈ B
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem (hle _ a.2) hu }
  let T : Submonoid (chartRing ℤ x c) :=
    { carrier := {u | ∃ b : ℕ, b ≠ 0 ∧ (u : Ω) = b}
      one_mem' := ⟨1, one_ne_zero, by simp⟩
      mul_mem' := by
        rintro u v ⟨b, hb, hu⟩ ⟨b', hb', hv⟩
        exact ⟨b * b', mul_ne_zero hb hb', by rw [Subalgebra.coe_mul, hu, hv]; push_cast; rfl⟩ }
  by_contra hcon
  have hdisj : Disjoint (I : Set (chartRing ℤ x c)) (T : Set (chartRing ℤ x c)) := by
    rw [Set.disjoint_left]
    rintro u hu ⟨b, hb, hub⟩
    have hu' : (b : Ω) * f ∈ B := by rw [← hub]; exact hu
    apply hcon
    have h2 := B.smul_mem hu' ((b : ℚ)⁻¹)
    have hb0 : (b : Ω) ≠ 0 := Nat.cast_ne_zero.2 hb
    have e : ((b : ℚ)⁻¹) • ((b : Ω) * f) = f := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, ← _root_.mul_assoc, inv_mul_cancel₀ hb0, _root_.one_mul]
    rwa [e] at h2
  obtain ⟨P, hP, hIP, hPT⟩ := Ideal.exists_le_prime_disjoint I T hdisj
  obtain ⟨p, hp, hpP⟩ := TieVB.exists_point hT hc P hP
  have h0 : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p := by
    intro r hr hfib
    have hrT : (r : chartRing ℤ x c) ∈ T := ⟨r, hr.ne_zero, by simp⟩
    have hnot : (r : chartRing ℤ x c) ∉ P := fun h => Set.disjoint_left.1 hPT h hrT
    have hu := not_not.1 (mt (hpP (r : chartRing ℤ x c)).2 hnot)
    apply hfib
    simpa using hu
  obtain ⟨s, hsA, hsu, hsf⟩ := TieVB.exists_den hT hp (hf p hp h0)
  have hI : (⟨s, hsA⟩ : chartRing ℤ x c) ∈ I := hle _ hsf
  exact (hpP ⟨s, hsA⟩).1 (hIP hI) hsu

theorem adjoin_segre_le {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} (c : (k : K) → ι k) :
    Algebra.adjoin ℚ (Set.range fun c' : (k : K) → ι k => (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) ≤
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨c', rfl⟩
  show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, c' k⟩, rfl⟩

theorem zpow_sum_of_ne {R : Type} {a : Ω} (ha : a ≠ 0) (s : Finset R) (f : R → ℤ) :
    a ^ (∑ r ∈ s, f r) = ∏ r ∈ s, a ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ ha, ih]

theorem eps_identity {K R : Type} [Fintype K] [Fintype R] {Y : K → Ω} (hY : ∀ k, Y k ≠ 0) (xd : R → K → ℤ)
    {e : R → Ω} (n : R → ℤ) (A : K → ℤ) (k₀ : K) (hA₀ : A k₀ = 1)
    (hA : ∀ k, k ≠ k₀ → A k = 0) (q : ℕ) (s : Ω) :
    (s * ∏ r, e r ^ n r) * ∏ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      s * Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) := by
  have h1 : ∀ k, Y k ^ (-(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k)) =
      (∏ r, (Y k ^ xd r k) ^ n r) * Y k ^ ((q : ℤ) * A k) := by
    intro k
    have e1 : -(∑ r, (-n r) * xd r k + (-(q : ℤ)) * A k) = ∑ r, xd r k * n r + (q : ℤ) * A k := by
      rw [neg_add, ← Finset.sum_neg_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun r _ => by ring
      · ring
    rw [e1, zpow_add₀ (hY k), zpow_sum_of_ne (hY k)]
    simp only [zpow_mul]
  have h2 : ∏ k, Y k ^ ((q : ℤ) * A k) = Y k₀ ^ q := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA k hk]; simp) (fun h => absurd (Finset.mem_univ _) h), hA₀]
    simp
  have h3 : ∏ r, ((∏ k, Y k ^ xd r k) * e r) ^ (-n r) =
      ((∏ k, ∏ r, (Y k ^ xd r k) ^ n r) * ∏ r, e r ^ n r)⁻¹ := by
    simp only [zpow_neg, Finset.prod_inv_distrib]
    congr 1
    simp only [mul_zpow, Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_comm]
    exact Finset.prod_congr rfl fun r _ => (Finset.prod_zpow _ _ _).symm
  simp only [h1, Finset.prod_mul_distrib]
  rw [h2, h3, div_inv_eq_mul]
  ring

end General

theorem section_on_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (nu : Wt (CMType H) (D.p + D.q)), (∀ r, (Fx.n r : ℝ) = (Fx.kA * Fx.q' : ℕ) * nu r.1 r.2) → ∃ (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ j, (n₀ j : ℝ) = (Fx.kA * Fx.q' : ℕ) * RM.coef nu (-1) j) ∧ 0 < N₀ ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 ∧ ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ∈ chartLatNm RM.y (combLine (RM.line 1) n₀).a 1 := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx o nu hn
  classical
  haveI : CharZero c.F := inferInstance
  haveI : CharZero RM.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hkA : (RM.kA : ℝ) = Fx.kA := by exact_mod_cast o.kA_eq
  have hkpos : (0 : ℝ) < Fx.kA := by rw [← hkA]; exact_mod_cast RM.kA_pos
  let n₀ : Option (RootIx D) → ℤ := fun j => j.elim (-(Fx.q' : ℤ)) fun r => -Fx.n r
  have hs0 : o.g Fx.sE * ∏ r, o.e r ^ Fx.n r ≠ 0 :=
    mul_ne_zero ((map_ne_zero o.g).2 Fx.sE_ne)
      (Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (o.lines r).1)
  have ha : ∀ k, (combLine (RM.line 1) n₀).a k =
      ∑ r, (-Fx.n r) * RM.xdeg r k + (-(Fx.q' : ℤ)) * RM.A.a k := by
    intro k
    show (∑ j, n₀ j • (RM.line 1 j).a) k = _
    rw [Finset.sum_apply, Fintype.sum_option, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun r _ => ?_
      simp [n₀, RootModel.line, RM.x_deg]
  have key : ∀ c' : ∀ k, RM.ι k, (∀ k, RM.y ⟨k, c' k⟩ ≠ 0) →
      IsIntegral (Algebra.adjoin ℚ (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩))
        ((o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k))) := by
    intro c' hc'
    have hx : (∏ k, RM.y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc' k
    have ya : o.g (Fx.yf (o.ix.symm (c' o.k₀))) = RM.y ⟨o.k₀, c' o.k₀⟩ := by
      rw [← o.y_eq, Equiv.apply_symm_apply]
    have hfeq : (o.g Fx.sE * ∏ r, o.e r ^ Fx.n r) * ∏ k, RM.y ⟨k, c' k⟩ ^ (-((combLine (RM.line 1) n₀).a k)) =
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) := by
      simp only [ha]
      rw [ya]
      exact eps_identity hc' RM.xdeg Fx.n RM.A.a o.k₀ o.A_deg.1 o.A_deg.2 Fx.q' _
    have hreg : ∀ p : Cpt o.𝔐.ξ, InChart o.𝔐.ξ (fun c'' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c'' k⟩) c' p →
        (∀ r : ℕ, r.Prime → ¬ InFibre o.𝔐.ξ r p) →
        o.g Fx.sE * o.g (Fx.yf (o.ix.symm (c' o.k₀))) ^ Fx.q' /
          ∏ r, ((∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) ^ (-Fx.n r) ∈ regAt o.𝔐.ξ p := by
      intro p hp hp0
      have hch : InChart o.𝔐.ξ (fun i' => o.g (Fx.yf i')) (o.ix.symm (c' o.k₀)) p := by
        refine ⟨?_, fun j => ?_⟩
        · show o.g (Fx.yf (o.ix.symm (c' o.k₀))) ≠ 0
          rw [ya]; exact hc' _
        · show o.g (Fx.yf j) / o.g (Fx.yf (o.ix.symm (c' o.k₀))) ∈ _
          rw [ya, ← o.y_eq]
          exact Lat.block_ratio_mem hp o.k₀ (o.ix j)
      have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (Λ := o.Fl.rootLat) (fun r => -Fx.n r) (p := p)
        (s := fun r => (∏ k, RM.y ⟨k, c' k⟩ ^ RM.xdeg r k) * o.e r) fun r =>
          ⟨mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc' k)) (o.lines r).1,
            (o.lines r).2 _ trivial c' hp⟩
      exact (o.eff p hp0 _ _ hch ht).1
    have hB := adjoin_segre_le c' (mem_adjoin_rat_of_regular o.𝔐.tie hx hreg)
    rw [hfeq]
    exact isIntegral_algebraMap (x := (⟨_, hB⟩ : Algebra.adjoin ℚ
      (Set.range fun p : Σ k, RM.ι k => RM.y p / RM.y ⟨p.1, c' p.1⟩)))
  obtain ⟨N₀, hN, hmem⟩ := GlobalTheory.T.integral_section_lattice_multiple RM.K RM.ι RM.Ω RM.y 0 (combLine (RM.line 1) n₀).a _ key
  refine ⟨n₀, N₀, ?_, hN, ?_, ?_⟩
  · intro j
    cases j with
    | none =>
      show ((-(Fx.q' : ℤ) : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-1 / (RM.kA : ℝ))
      rw [hkA]
      push_cast
      field_simp
    | some r =>
      show ((-Fx.n r : ℤ) : ℝ) = ((Fx.kA * Fx.q' : ℕ) : ℝ) * (-nu r.1 r.2)
      push_cast
      rw [hn r]
      push_cast
      ring
  · rw [_root_.mul_assoc]
    exact mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') hs0
  · rw [_root_.mul_assoc]
    exact hmem

end GlobalTheory.CompanionTheory.Ar.Small.OriginEps
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem ip_add_left' (R : RiemLat E g Λ) (x x' y : Fin g → ℂ) : R.ip (x + x') y = R.ip x y + R.ip x' y := by
  simp [RiemLat.ip, star_add, Matrix.mulVec_add, dotProduct_add]

theorem ip_add_right' (R : RiemLat E g Λ) (x y y' : Fin g → ℂ) : R.ip x (y + y') = R.ip x y + R.ip x y' := by
  simp [RiemLat.ip, add_dotProduct]

theorem ip_smul_left' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) :
    R.ip (c • x) y = star c * R.ip x y := by
  simp [RiemLat.ip, star_smul, Matrix.mulVec_smul, dotProduct_smul]

theorem ip_smul_right' (R : RiemLat E g Λ) (c : ℂ) (x y : Fin g → ℂ) : R.ip x (c • y) = c * R.ip x y := by
  simp [RiemLat.ip, smul_dotProduct]

theorem real_smul_eq' (r : ℝ) (x : Fin g → ℂ) : r • x = (r : ℂ) • x := by
  ext i
  simp

theorem ip_period_im (R : RiemLat E g Λ) (x y : Λ) : (R.ip (R.P x) (R.P y)).im = R.form y x :=
  R.im y x

theorem isometry_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hf : ∀ x y, R'.form (γ x) (γ y) = R.form x y) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (x y : Fin g → ℂ) : R'.ip (φ x) (φ y) = R.ip x y := by
  let D : (Fin g → ℂ) → (Fin g → ℂ) → ℂ := fun z w => R'.ip (φ z) (φ w) - R.ip z w
  have hl : ∀ z z' w, D (z + z') w = D z w + D z' w := fun z z' w => by
    simp only [D, map_add (f := _), ip_add_left']
    ring
  have hr : ∀ z w w', D z (w + w') = D z w + D z w' := fun z w w' => by
    simp only [D, map_add (f := _), ip_add_right']
    ring
  have hcl : ∀ (c : ℂ) z w, D (c • z) w = star c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_left']
    ring
  have hcr : ∀ (c : ℂ) z w, D z (c • w) = c * D z w := fun c z w => by
    simp only [D, map_smul, ip_smul_right']
    ring
  have h0l : ∀ w, D 0 w = 0 := fun w => by
    simp [D, RiemLat.ip]
  have h0r : ∀ z, D z 0 = 0 := fun z => by
    simp [D, RiemLat.ip]
  have base : ∀ l l', (D (R.P l) (R.P l')).im = 0 := fun l l' => by
    simp only [D, Complex.sub_im]
    rw [← hP, ← hP, ip_period_im, ip_period_im, hf, sub_self]
  have s1 : ∀ l w, (D (R.P l) w).im = 0 := fun l w => by
    have hw : w ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w h =>
      obtain ⟨l', rfl⟩ := h
      exact base l l'
    | zero => simp [h0r]
    | add w w' _ _ h h' => simp [hr, h, h']
    | smul r w _ h =>
      rw [real_smul_eq', hcr]
      simp [h]
  have s2 : ∀ z w, (D z w).im = 0 := fun z w => by
    have hz : z ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨l, rfl⟩ := h
      exact s1 l w
    | zero => simp [h0l]
    | add z z' _ _ h h' => simp [hl, h, h']
    | smul r z _ h =>
      rw [real_smul_eq', hcl]
      simp [h]
  have s3 : (D x y).re = 0 := by
    have h := s2 x (Complex.I • y)
    rw [hcr] at h
    simpa using h
  have s4 : D x y = 0 := Complex.ext s3 (s2 x y)
  exact sub_eq_zero.mp s4

theorem commutes_of_periods (R R' : RiemLat E g Λ) (hs : Submodule.span ℝ (Set.range R.P) = ⊤)
    (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hP : ∀ x, R'.P (γ x) = φ (R.P x))
    (a : 𝓞 E) (x : Fin g → ℂ) : φ (R.B a x) = R'.B a (φ x) := by
  have hx : x ∈ Submodule.span ℝ (Set.range R.P) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨l, rfl⟩ := h
    rw [← R.act, ← hP, ← hP, map_smul, R'.act]
  | zero => simp
  | add x x' _ _ h h' => simp [h, h']
  | smul r x _ h =>
    rw [real_smul_eq', map_smul, map_smul, h, map_smul, map_smul]

theorem isometry_and_commutes : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
    (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) →
    (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  intro E _ _ _ g Λ _ _ R R' γ φ hf hP
  have hs := (GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R).2.1
  exact ⟨isometry_of_periods R R' hs γ φ hf hP, commutes_of_periods R R' hs γ φ hP⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

theorem span_eq_top :
    Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hφ0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective
  have hc := Fintype.linearIndependent_iff.1 li
    (fun t => φ fun j => if t = j then 1 else 0) (by
      funext a
      have h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0 :=
        hφ (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ] at h0
      simpa [chr, Finset.sum_apply, mul_comm] using h0)
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ w]
  simp only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]


open Classical in
theorem exists_coeffs (s : 𝓞 E →+* ℂ) : ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ),
    ∀ t : E →+* ℂ, ∑ i, c i * t (algebraMap (𝓞 E) E (a i)) = if t = extend s then 1 else 0 := by
  have hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨f.support.card, fun i => (f.support.equivFin.symm i).1,
    fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩
  have ht := congrFun hf t
  rw [Finsupp.sum, Finset.sum_apply] at ht
  rw [← ht]
  refine (Equiv.sum_comp f.support.equivFin.symm
    (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_
  exact Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))

theorem eigComp_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ),
    ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  classical
  intro E _ _ _ s
  obtain ⟨N, a, c, h⟩ := exists_coeffs s
  refine ⟨N, a, c, ?_⟩
  intro g Λ _ _ R z
  obtain ⟨-, -, hs, hsum, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) =
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b t
    have hm := (hs (t.comp (algebraMap (𝓞 E) E))).1 z
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm
    have := hm b
    simpa [sub_eq_zero] using this
  have hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ,
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b
    conv_lhs => rw [← hsum z]

    rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => hB b t
  calc eigComp R.B s z
      = ∑ t : E →+* ℂ, (if t = extend s then (1 : ℂ) else 0) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp [extend_comp]
    _ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [h]
    _ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ i, c i • R.B (a i) z := by simp only [hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula
end
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.slope_bound_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound | exact GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound <;> assumption)
end

section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

theorem _root_.GlobalTheory.T.orthogonal_flag_degree_comparison : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ j k), A.IsOrthFull → -E.normDegree ⊤ - ∑ τ, A.flatDeg τ ≤ 2 * ∑ τ, -E.normDegree (A.W τ).top ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ ⨆ a, A.part a) → 2 * ∑ τ, -E.normDegree (A.W τ).top ≤ -E.normDegree ⊤ - ∑ τ, A.flatDeg τ + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | exact GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagPair.two_sum_neg_degree_W <;> assumption)
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.ball_mobius_holomorphic_potential_change : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → DifferentiableOn ℂ (moebBall q u) (ballDom q) ∧ Set.MapsTo (moebBall q u) (ballDom q) (ballDom q) ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G (ballDom q) ∧ ∀ t ∈ ballDom q, ballPot q (moebBall q u t) = ballPot q t + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Moeb.moebBall_props <;> assumption)
end
