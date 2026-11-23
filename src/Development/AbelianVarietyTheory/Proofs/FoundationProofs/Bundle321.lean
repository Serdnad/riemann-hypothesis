module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle316
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRootNear
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle060
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle025
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle064
public import Formalism.SatakeDualWeyl.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle317
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryIwasawaCellBoundSmallTorusDoubleCoset
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalHermitianOfDiagPosIsSquare
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaSpan

open GlobalTheory.TripleIntertwiner

section
variable {V : Type*} [AddCommGroup V] {F : Type} [AddCommGroup F] [Module ℂ F]

theorem sum_translate {M : Type} [AddCommMonoid M] {A₀ A : AddSubgroup V} [Fintype (A ⧸ A₀.addSubgroupOf A)]
    (g : V → M) (hg : ∀ x ∈ A, ∀ l ∈ A, l ∈ A₀ → g (x + l) = g x) {a : V} (ha : a ∈ A) :
    ∑ q : A ⧸ A₀.addSubgroupOf A, g (a + rep q) = ∑ q : A ⧸ A₀.addSubgroupOf A, g (rep q) := by
  let q₀ : A ⧸ A₀.addSubgroupOf A := QuotientAddGroup.mk ⟨a, ha⟩
  rw [← Equiv.sum_comp (Equiv.addLeft q₀) (fun q => g (rep q))]
  refine Finset.sum_congr rfl fun q _ => ?_
  obtain ⟨l, hl0, hl, h3⟩ := rep_add q₀ q
  obtain ⟨l', hl0', hl', h4⟩ := rep_mk (B := A₀) (⟨a, ha⟩ : A)
  show _ = g (rep (q₀ + q))
  rw [h3, hg _ (add_mem (rep_mem _) (rep_mem _)) _ hl0 hl, h4, add_right_comm,
    hg _ (add_mem ha (rep_mem _)) _ hl0' hl']

variable {W : V → F →ₗ[ℂ] F} {c : V → V → ℂ}

theorem mem_span_translates (H : (∀ x y f, W x (W y f) = c x y • W (x + y) f) ∧
      (∀ x x' y, c (x + x') y = c x y * c x' y) ∧ (∀ x y y', c x (y + y') = c x y * c x y') ∧
      ∀ x y, c x y ≠ 0) (W0 : ∀ f, W 0 f = f)
    {A : AddSubgroup V} (m : ℕ) (s : V →+ V) (hs : ∀ v, m • s v = v) (hs' : ∀ v, s (m • v) = v)
    [Fintype (A ⧸ (subLa m A).addSubgroupOf A)] (cA : ∀ x ∈ A, ∀ y ∈ A, c x y = 1)
    (hsd : ∀ v, (∀ x ∈ A, c x v = c v x) → v ∈ A)
    (P : Submodule ℂ F) (hP : ∀ x, ∀ f ∈ P, W x f ∈ P) (e : F)
    (line : ∀ g ∈ P, (∀ x ∈ A, W x g = g) → ∃ t : ℂ, g = t • e)
    (f : F) (hfP : f ∈ P) (hf : ∀ x ∈ A, W (m • x) f = f) :
    f ∈ Submodule.span ℂ {g | ∃ a ∈ A, g = W (s a) e} := by
  obtain ⟨H1, H2, H3, H4⟩ := H
  have c0 : ∀ y, c 0 y = 1 := fun y => by
    have := H2 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 0 y)).1 this.symm
  have c0' : ∀ y, c y 0 = 1 := fun y => by
    have := H3 y 0 0
    rw [add_zero] at this
    exact (mul_eq_left₀ (H4 y 0)).1 this.symm
  have cm : ∀ (k : ℕ) x y, c (k • x) y = c x (k • y) := by
    intro k x y
    induction k with
    | zero => rw [zero_smul, zero_smul, c0, c0']
    | succ k ih => rw [succ_nsmul, succ_nsmul, H2, H3, ih]
  have cs : ∀ x y, c (s x) y = c x (s y) := fun x y => by
    conv_lhs => rw [← hs y, ← cm, hs]
  have comm : ∀ x y g, W x (W y g) = (c x y / c y x) • W y (W x g) := by
    intro x y g
    rw [H1, H1, smul_smul, div_mul_cancel₀ _ (H4 _ _), add_comm]
  have hA0 : ∀ l ∈ subLa m A, ∃ x ∈ A, l = m • x := by
    rintro l ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  let G : V → F := fun a => ∑ q : A ⧸ (subLa m A).addSubgroupOf A, W (rep q) (W (s (-a)) f)
  have hG : ∀ a ∈ A, ∃ t : ℂ, G a = t • e := by
    intro a ha
    refine line _ (P.sum_mem fun q _ => hP _ _ (hP _ _ hfP)) fun x hx => ?_
    have := sum_translate (A₀ := subLa m A) (fun y => W y (W (s (-a)) f)) (fun y hy l hl hl' => by
      obtain ⟨b, hb, rfl⟩ := hA0 l hl'
      have h1 : W (m • b) (W (s (-a)) f) = W (s (-a)) f := by
        rw [comm, hf b hb, cm, ← cm m (s _), hs, cA _ hb _ (neg_mem ha), cA _ (neg_mem ha) _ hb]; simp
      have h2 := H1 y (m • b) (W (s (-a)) f)
      rw [h1, cA _ hy _ hl, one_smul] at h2
      exact h2.symm) hx

    simp only [G, map_sum]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [H1, cA _ hx _ (rep_mem q), one_smul]
  have hWG : ∀ a, (c (s a) (s (-a)))⁻¹ • W (s a) (G a) =
      ∑ q : A ⧸ (subLa m A).addSubgroupOf A, (c a (s (rep q)) / c (s (rep q)) a) • W (rep q) f := by
    intro a

    simp only [G, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [comm, H1 (s a), ← map_add (f := _), add_neg_cancel, map_zero, W0, map_smul, smul_smul, smul_smul, cs a (rep q),
      ← cs (rep q) a]
    congr 1
    have := H4 (s a) (s (-a))
    field_simp
  have hχ : ∀ q : A ⧸ (subLa m A).addSubgroupOf A,
      (∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u)) • W (rep q) f =
        if q = 0 then (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f else 0 := by
    intro q
    split_ifs with h
    · obtain ⟨l, -, hl, h3⟩ := rep_mk (B := subLa m A) (0 : A)
      obtain ⟨b, hb, rfl⟩ := hA0 l hl
      have h4 : rep q = m • b := by rw [h]; simpa using h3
      have h5 : s (rep q) = b := by rw [h4, hs']
      rw [h5, h4, hf b hb, Finset.sum_congr rfl (g := fun _ => (1 : ℂ)) fun u _ => by
        rw [cA _ hb _ (rep_mem u), cA _ (rep_mem u) _ hb, div_one]]
      simp
    · have hv : s (rep q) ∉ A := by
        intro hv
        apply h
        rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
        exact ⟨_, hv, hs _⟩
      obtain ⟨x₀, hx₀, hne⟩ : ∃ x ∈ A, c x (s (rep q)) ≠ c (s (rep q)) x := by
        by_contra hh
        push_neg at hh
        exact hv (hsd _ hh)
      have := sum_translate (A₀ := subLa m A) (fun y => c y (s (rep q)) / c (s (rep q)) y) (fun y hy l hl hl' => by
        obtain ⟨b, hb, rfl⟩ := hA0 l hl'
        simp only [H2, H3]
        rw [cm, ← cm m (s _), hs, cA _ hb _ (rep_mem q), cA _ (rep_mem q) _ hb, mul_one, mul_one]) hx₀
      simp only [H2, H3, mul_div_mul_comm, ← Finset.mul_sum] at this
      have h1 : c x₀ (s (rep q)) / c (s (rep q)) x₀ ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq (H4 _ _)]; exact hne
      have h2 : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, c (rep u) (s (rep q)) / c (s (rep q)) (rep u) = 0 := by
        by_contra h0
        exact h1 ((mul_eq_right₀ h0).1 this)
      rw [h2, zero_smul]
  have hsum : ∑ u : A ⧸ (subLa m A).addSubgroupOf A, (c (s (rep u)) (s (-rep u)))⁻¹ • W (s (rep u)) (G (rep u)) =
      (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) • f := by
    simp only [hWG]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hχ]
    simp
  have hc : (Fintype.card (A ⧸ (subLa m A).addSubgroupOf A) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Submodule.smul_mem_iff _ hc, ← hsum]
  refine Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ ?_
  obtain ⟨t, ht⟩ := hG _ (rep_mem u)
  rw [ht, map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rep_mem u, rfl⟩)

end

theorem wd_differentiable (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {G : VC D N N' → ℂ}
    (hG : Differentiable ℂ G) : Differentiable ℂ (Wd D T x G) := by
  unfold Wd U Hf
  fun_prop

theorem theta_span : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ F ∈ TT D (tor0 D cc δ) N N', ∃ (k : ℕ) (r : Fin k → ℂ) (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), F = ∑ i, r i • Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ (z i)) e0 := by
  intro D cc δ hc N N' e0 he he0 F hF
  obtain ⟨hFd, m, hm, hF⟩ := hF
  have hSD : ∀ n, SD D (stdL D n) := fun n => by
    obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
    rw [← h2]; exact (h1 _).2
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, hSD N, hSD N', rfl⟩
  have hg := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨l1, l2, -, l4, l5, -, -⟩ := GlobalTheory.ThetaLine.theta_line D hg cc δ hc N N' _ k
  have hrat := fun x hx => GlobalTheory.ThetaInter.klat_rat hg.1 k (x := x) hx
  change e0 ∈ ThSp D _ (La0 D (tor0 D cc δ) N N') at he
  set A := La0 D (tor0 D cc δ) N N'
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot l5 fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI : Fintype (A ⧸ (subLa m A).addSubgroupOf A) := Fintype.ofFinite _
  have H := wLin_heis D (tor0 D cc δ) (N := N) (N' := N')
  have fix : ∀ x ∈ A, wLin D (tor0 D cc δ) x e0 = e0 := fun x hx => by
    show Wd D _ x e0 = e0
    rw [l2 x hx]
    exact funext (he.2 x hx)
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  let P : Submodule ℂ (VC D N N' → ℂ) :=
    { carrier := {G | Differentiable ℂ G}
      add_mem' := fun ha hb => Differentiable.add ha hb
      zero_mem' := differentiable_const _
      smul_mem' := fun a _ h => Differentiable.const_smul h a }
  have key := mem_span_translates (c := fun x y => Complex.exp (cocExp D (tor0 D cc δ) x y)) H
    (fun f => wd_zero D _ f) (A := A) m (DistribSMul.toAddMonoidHom _ (m : ℂ)⁻¹)
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun v => by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hm'])
    (fun x hx y hy => by
      have := H.1 x y e0
      rw [fix y hy, fix x hx, fix _ (A.add_mem hx hy)] at this
      exact smul_left_injective ℂ he0 (this.symm.trans (one_smul ℂ e0).symm))
    (fun v hv => l4 v fun y hy => im_int_of_comm D _ y v (hv y hy))
    P (fun x f hf => wd_differentiable D _ x hf) e0
    (fun g hg hfix => l1 g ⟨hg, fun x hx z => by
      have := hfix x hx
      change Wd D _ x g = g at this
      rw [l2 x hx] at this
      exact congrFun this z⟩ e0 he he0)
    F hFd hF
  obtain ⟨n, r, g, hsum⟩ := Submodule.mem_span_set'.1 key
  have : ∀ i, ∃ z, (g i : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) e0 := by
    intro i
    obtain ⟨a, ha, h⟩ := (g i).2
    obtain ⟨B, rfl⟩ := hrat a ha
    refine ⟨((m : D.host.K)⁻¹) • B, h.trans ?_⟩
    unfold pt
    rw [GlobalTheory.ThetaInter.embV_smul hg.1, smul_comm δ]
    simp [wLin]
  choose z hz using this
  exact ⟨n, r, z, by rw [← hsum]; simp only [hz]⟩

end GlobalTheory.ThetaSpan
end
end

section

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.AdLat.RootNear
open scoped TensorProduct

namespace GlobalTheory.OddRoot

theorem finite_root_odd (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1)
    (hP : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ t s : 𝓞 E, (s : E) = c (t : E) ∧ t - s ∉ P) (n : ℕ)
    (hn : Odd n) (u z : RA F E) (hz : z ∈ intHat F E) (huz : u - 1 = n • z)
    (hu : u * sg (FiniteAdeleRing (𝓞 F) F) c u = 1) :
    ∃ x y : RA F E, x ∈ intHat F E ∧ y ∈ intHat F E ∧ x * y = 1 ∧
      x = u * sg (FiniteAdeleRing (𝓞 F) F) c x ∧ ∃ p ∈ intHat F E, x - 1 = n • p := by
  have hu1 : u = 1 + n * z := by
    rw [nsmul_eq_mul] at huz
    linear_combination huz
  have huO : u ∈ intHat F E := by
    rw [hu1]
    exact add_mem (one_mem _) (mul_mem (natCast_mem _ n) hz)
  obtain ⟨x₁, hx₁, ⟨y₁, hy₁, hxy₁⟩, hr₁⟩ := GlobalTheory.T.exists_integral_unit_root_norm_one_adele F E c h2 hc hP u huO hu
  obtain ⟨e, f, hee, hef, hun⟩ :=
    exists_idem (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F) n
  obtain ⟨h, hh⟩ : ∃ h, e = 2 * h := by
    obtain ⟨g, hg⟩ := (hun (-1)).exists_right_inv
    obtain ⟨k, hk⟩ := hn
    refine ⟨-(k * e * g), ?_⟩
    rw [hk] at hg
    push_cast at hg
    linear_combination (-e) * hg - (2 * k + 1) * g * hee
  obtain ⟨y₀, hy₀⟩ := (unit_of_integral (inclHat F E) (inclHat_integral F E) (e * n) hun
    (inclHat F E h * ⟨z, hz⟩)).exists_right_inv
  have hse : sg (FiniteAdeleRing (𝓞 F) F) c (inclHat F E e : RA F E) = (inclHat F E e : RA F E) := by
    change sg (FiniteAdeleRing (𝓞 F) F) c (incl F e ⊗ₜ[F] (1 : E)) = incl F e ⊗ₜ[F] (1 : E)
    simp [sg]
  have hee' : (inclHat F E e : RA F E) * inclHat F E e = inclHat F E e := by
    rw [← Subring.coe_mul, ← map_mul, hee]
  have hef' : 1 - (inclHat F E e : RA F E) = n * inclHat F E f := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hef
    simpa using this
  have hh' : (inclHat F E e : RA F E) = 2 * inclHat F E h := by
    have := congrArg (fun t => (inclHat F E t : RA F E)) hh
    simp only [map_mul, map_ofNat] at this
    exact this
  have hy₀' : (1 + (inclHat F E e : RA F E) * n * (inclHat F E h * z)) * y₀ = 1 := by
    have := congrArg (fun t : intHat F E => (t : RA F E)) hy₀
    simpa using this
  have heO := (inclHat F E e).2
  have hfO := (inclHat F E f).2
  have hhO := (inclHat F E h).2
  have hy₀O := y₀.2
  generalize (inclHat F E e : RA F E) = e' at *
  generalize (inclHat F E f : RA F E) = f' at *
  generalize (inclHat F E h : RA F E) = h' at *
  generalize (y₀ : RA F E) = y' at *
  have hx₁' : x₁ ∈ intHat F E := hx₁
  have hy₁' : y₁ ∈ intHat F E := hy₁
  obtain ⟨w, hw⟩ : ∃ w, w = 1 + e' * n * (h' * z) := ⟨_, rfl⟩
  rw [← hw] at hy₀'
  have hwO : w ∈ intHat F E := by
    rw [hw]
    exact add_mem (one_mem _) (mul_mem (mul_mem heO (natCast_mem _ n)) (mul_mem hhO hz))
  have h2w : 2 * (e' * w) = e' * (1 + u) := by
    rw [hw, hu1]
    linear_combination (-(e' * e' * n * z)) * hh' + (n * z * (e' + 1)) * hee'
  have hr₀ : e' * w = u * sg (FiniteAdeleRing (𝓞 F) F) c (e' * w) := by
    have htwo : IsUnit (2 : RA F E) := by
      have := (IsUnit.mk0 (2 : F) two_ne_zero).map (algebraMap F (RA F E))
      rwa [map_ofNat] at this
    apply htwo.mul_left_cancel
    have := congrArg (sg (FiniteAdeleRing (𝓞 F) F) c) h2w
    rw [map_mul _ 2, map_ofNat, map_mul _ e' (1 + u), map_add (f := _), map_one, hse] at this
    linear_combination h2w - u * this - e' * hu
  have he1 := sub_mem (one_mem (intHat F E)) heO
  refine ⟨e' * w + (1 - e') * x₁, e' * y' + (1 - e') * y₁, add_mem (mul_mem heO hwO) (mul_mem he1 hx₁'),
    add_mem (mul_mem heO hy₀O) (mul_mem he1 hy₁'), ?_, ?_, e' * e' * (h' * z) + f' * (x₁ - 1),
    add_mem (mul_mem (mul_mem heO heO) (mul_mem hhO hz)) (mul_mem hfO (sub_mem hx₁' (one_mem _))), ?_⟩
  · linear_combination e' * hy₀' + (1 - e') * hxy₁ + (w * y' - w * y₁ - x₁ * y' + x₁ * y₁) * hee'
  · rw [map_add (f := _), map_mul _ (1 - e'), map_sub, map_one, hse]
    linear_combination hr₀ + (1 - e') * hr₁
  · rw [nsmul_eq_mul, hw]
    linear_combination (x₁ - 1) * hef'

end GlobalTheory.OddRoot
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OddRoot
open GlobalTheory.Member

theorem exists_root_odd : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  intro D N hN u z hz huz hu
  have hP : ∀ P : Ideal (𝓞 D.host.E), P.IsMaximal →
      ∃ t s : 𝓞 D.host.E, (s : D.host.E) = cF D (t : D.host.E) ∧ t - s ∉ P := by
    intro P hP
    obtain ⟨θ, t, ht, hθ⟩ := D.sp.cm.cmUnram.2.2 P hP
    exact ⟨θ, t, ht, hθ⟩
  have hc : cF D ≠ 1 := by
    intro h
    obtain ⟨P, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
    obtain ⟨t, s, hs, hts⟩ := hP P hM
    rw [h] at hs
    have : s = t := Subtype.ext hs
    rw [this, sub_self] at hts
    exact hts P.zero_mem
  rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hz ⊢
  exact finite_root_odd D.host.F D.host.E (cF D) D.sp.cm.deg2 hc hP N hN u z hz huz hu

end GlobalTheory.OddRoot
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField
open GlobalTheory.IndefiniteRowSideFullHecke.RationalFormValues

namespace GlobalTheory.Proof.PlaceExtensionValues

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Coef

variable {K K' : Type} [Field K] [Field K'] {σ : K →+* ℂ} {σ' : K' →+* ℂ} {ι : K →+* K'}
  {I : Type} [Fintype I] {n : ℕ} {lam : I → DomWeight n} {W : Type} [AddCommGroup W] [Module ℂ W]
  {c₀ : VV K lam →ₛₗ[σ] W} {c' : VV K' lam →ₛₗ[σ'] W}

end Coef

section Reps

variable {Gp Γ : Type} [Group Gp] [Group Γ] {ι : Γ →* Gp} {J : Subgroup Gp}


end Reps

section Row

open Formalism.IndefR.FWT

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T)
  {K' : Type} [Field K'] {σ' : K' →+* ℂ}

theorem isCoefExt_iff_c0BC (jL : D.what₂.LL →+* K') (c₀ : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) :
    IsCoefExt jL (FWT.lamV D i) c₀ c' ↔ CoefficientBaseChange R i jL σ' c₀ c' := by
  constructor
  · intro h v
    exact ⟨⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV jL _ _ v.2⟩, rfl, h v _ rfl⟩
  · intro h v v' hv
    obtain ⟨w, hw, hc⟩ := h v
    rw [show v' = w from Subtype.ext (hv.trans hw.symm)]
    exact hc

variable (c' : VsV D i K' →ₛₗ[σ'] (R.cV i).W)

variable {R i t c'}

variable {gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E}
  {c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W}
  {c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W} {jL : D.what₂.LL →+* K'}


variable (R)

end Row

end GlobalTheory.Proof.PlaceExtensionValues

end
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitarySatakeTransform_isLaurentPolynomial : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ h ∈ Hecke ℂ (KU σ n), ∃ s : (Fin (n / 2) → ℤ) →₀ ℂ, (∀ α : Fin (n / 2) → ℂ, SatU ϖ q h α = s.sum fun a c => c * ∏ i, α i ^ a i) ∧ (∀ κ, s κ ≠ 0 → ∃ g : GU σ n, h g ≠ 0 ∧ ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) ∧ ∀ (t : GU σ n) (ε : Fin (n / 2) → ℤ), ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = tMat ϖ n (n / 2) ε → h = dosetInd ℂ (KU σ n) t → s ε ≠ 0 := by
  first | exact @GlobalTheory.LFun.SatCoef.satU_laurent | exact GlobalTheory.LFun.SatCoef.satU_laurent | (intros; apply GlobalTheory.LFun.SatCoef.satU_laurent <;> assumption)
end

section

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

theorem _root_.GlobalTheory.T.unitaryIwasawaCell_bound_small_torusDoubleCoset : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (ε κ : Fin (n / 2) → ℤ) (u k k₁ k₂ : GU σ n), (∀ i, |ε i| ≤ 1) → IsUnipU u → k ∈ KU σ n → k₁ ∈ KU σ n → k₂ ∈ KU σ n → tMat ϖ n (n / 2) κ * ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((k₁ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * tMat ϖ n (n / 2) ε * ((k₂ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) → (∀ i, |κ i| ≤ 1) ∧ ∑ i, |κ i| ≤ ∑ i, |ε i| := by
  first | exact @GlobalTheory.LFun.CellBound.cell_bound | exact GlobalTheory.LFun.CellBound.cell_bound | (intros; apply GlobalTheory.LFun.CellBound.cell_bound <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_orthonormal_hermitian_of_diag_pos_isSquare : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (σ : K →+* K) (h : V →ₗ[K] V →ₛₗ[σ] K) (d : ℕ) (θ : K), 0 < d → θ ^ 2 = -(d : K) → σ θ = -θ → (∀ x : K, ∃ a b : ℚ, x = (a : K) + (b : K) * θ) → ∀ (r : ℕ) (v : Fin r → V) (a : Fin r → ℚ), (∀ i, 0 < a i) → (∀ i j, h (v i) (v j) = if i = j then (a i : K) else 0) → IsSquare (∏ i, a i) → ∃ e : Fin r → V, ∀ i j, h (e i) (e j) = if i = j then 1 else 0 := by
  first | exact @GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare | exact GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare | (intros; apply GlobalTheory.SqDet.exists_orthonormal_of_diag_pos_isSquare <;> assumption)
end
