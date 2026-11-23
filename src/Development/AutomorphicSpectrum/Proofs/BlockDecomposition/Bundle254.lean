module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import GroundTheory.GlobalFields.TateThesis.TateMain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import GroundTheory.AutomorphicForms.GL2.GodementSection
import GroundTheory.AutomorphicForms.GL2.SummableNormIffAndTsumEqCoset2
import GroundTheory.AutomorphicForms.LocallyProfinite

@[expose] public section

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEisMG

open MeasureTheory Topology

section SlopeTestRemainingChoices

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem leftGood_map {f : ℂ → X} {a : ℝ} (T : X →L[ℂ] Y) (h : LeftGood f a) :
    LeftGood (fun z => T (f z)) a := by
  refine ⟨T.differentiable.comp_differentiableOn h.1, fun b c hc => ?_⟩
  obtain ⟨M, hM⟩ := h.2 b c hc
  exact ⟨‖T‖ * M, fun z h1 h2 =>
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hM z h1 h2) (norm_nonneg _))⟩

theorem leftGood_mono {f : ℂ → X} {a b : ℝ} (hab : b ≤ a) (h : LeftGood f a) : LeftGood f b :=
  ⟨h.1.mono fun _ hz => lt_of_lt_of_le hz hab, fun b' c hc => h.2 b' c (lt_of_lt_of_le hc hab)⟩

end SlopeTestRemainingChoices

section Eis

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem eis_smul (Γ K P : Subgroup G) (c : G → ℂ) (ρ : K →* (W →L[ℂ] W)) (Λ : G → ℂ) (g : G)
    (t : ℂ) (w : W) : eis Γ K P c ρ Λ g (t • w) = t • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [map_smul, smul_comm]

end Eis

theorem master : AvgMem → DGood → HGood → BGood → Master := by
  intro hM hD hH hB
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hHaar hProb Γ P P' c η η' β L J R N Φ a ζ hpar hLe hR
    hcR hcL hΦ ha haN hζ hLaw hEqR hEqL
  obtain ⟨pr, hpr⟩ : (secSp K P' c ρ).ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional _
  let T : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] secSp K P' c ρ) :=
    ((ContinuousLinearMap.compL ℂ L W _).flip J).comp (ContinuousLinearMap.compL ℂ W W _ pr)
  let TJ : (W →L[ℂ] W) →L[ℂ] (L →L[ℂ] W) := (ContinuousLinearMap.compL ℂ L W W).flip J
  obtain ⟨hHd, hHc, hHb⟩ := hH G W K ρ hK hρ μ hHaar hProb Φ hΦ
  obtain ⟨hB1, hB2⟩ := hB G W K ρ hK hρ μ hHaar hProb ζ hζ
  obtain ⟨-, hD2⟩ := hD a N ha
  have hop : LeftGood (fun z : ℂ =>
      z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) (-R) := by
    have h2 := leftGood_map T hB2
    have e : (fun z : ℂ => T (z • (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) =
        fun z : ℂ => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)) :=
      funext fun z => map_smul T z _
    rw [e] at h2
    exact leftGood_mono (by linarith) h2
  refine ⟨fun z => z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    fun z g => TJ ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ fun κ => Φ z (g * κ)), ?_,
    fun _ _ _ => rfl, fun z => T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z)),
    leftGood_map T hB1, fun _ _ => rfl⟩
  refine
    { le := hLe, pos := hR, convR := hcR, convL := hcL, dEnt := hD2, dNe := ?_, op := hop
      hol := fun g => TJ.differentiable.comp (hHd g)
      cont := TJ.continuous.comp hHc
      bdd := ?_, eqR := ?_, eqL := ?_ }
  · obtain ⟨z, hz, haz⟩ := haN
    exact ⟨z, mul_ne_zero (sub_ne_zero.2 hz) (mul_ne_zero (Complex.exp_ne_zero _) haz)⟩
  · intro b a' g
    obtain ⟨U, hU, M, hMb⟩ := hHb b a' g
    exact ⟨U, hU, ‖TJ‖ * M, fun z h1 h2 g' hg' =>
      (TJ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hMb z h1 h2 g' hg') (norm_nonneg _))⟩
  · intro z hz g w
    have h := hEqR z hz g w
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) = _
    rw [mul_smul, h, smul_smul]
    congr 1
    ring
  · intro z hz g w
    have hz' : z.re < 1 / 2 := by linarith
    have hcont : Continuous (ζ z) := by
      have h1 : Continuous fun t : K => (z, t) := by fun_prop
      exact hζ.cont.comp_continuous h1 fun t => ⟨hz', Set.mem_univ _⟩
    have hmem : avg μ ρ (ζ z) (J w) ∈ secSp K P' c ρ :=
      hM G W K ρ hK hρ μ hHaar hProb Γ P' c hpar (ζ z) hcont (hLaw z) (J w)
    have hOp : (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W) =
        (z * (Complex.exp (z ^ 2) * (z - 1))) • avg μ ρ (ζ z) (J w) := by
      have hp : ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) =
          (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w) :=
        congrArg Subtype.val
          (hpr ⟨_, (secSp K P' c ρ).smul_mem (Complex.exp (z ^ 2) * (z - 1)) hmem⟩)
      change z • ((pr ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z) (J w)) : secSp K P' c ρ) : W) = _
      rw [hp, mul_smul z]
    change (Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (fun κ => Φ z (g * κ)) (J w) =
      eis Γ K P' c ρ (fun x => β x - z * η' x) g
        (((z • T ((Complex.exp (z ^ 2) * (z - 1)) • avg μ ρ (ζ z))) w : secSp K P' c ρ) : W)
    rw [hOp, eis_smul, hEqL z hz g (J w), smul_smul, mul_comm z]

end GlobalTheory.CompanionTheory.RgEisMG
end
end

section

noncomputable section
open NumberField IsDedekindDomain Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

namespace GlobalTheory.CompanionTheory.RgEis.InMTopPf

variable {k : Type} [Field k] [NumberField k]

theorem natCast_isUnit (M : ℕ) (hM : M ≠ 0) : IsUnit (M : FiniteAdeleRing (𝓞 k) k) := by
  have : (M : FiniteAdeleRing (𝓞 k) k) = algebraMap k _ (M : k) := by simp
  rw [this]
  exact (IsUnit.mk0 _ (by exact_mod_cast hM)).map _

theorem inM_iff (M : ℕ) (hM : M ≠ 0) (x : FiniteAdeleRing (𝓞 k) k) :
    InM M x ↔ (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
      FiniteAdeleRing (𝓞 k) k) * x ∈ OH k := by
  set u := (natCast_isUnit (k := k) M hM).unit
  have hu : (u : FiniteAdeleRing (𝓞 k) k) = M := rfl
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

theorem isOpen_isClosed (M : ℕ) (hM : M ≠ 0) :
    IsOpen {x : FiniteAdeleRing (𝓞 k) k | InM M x} ∧ IsClosed {x : FiniteAdeleRing (𝓞 k) k | InM M x} := by
  have hS : {x : FiniteAdeleRing (𝓞 k) k | InM M x} =
      (fun x => (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) :
        FiniteAdeleRing (𝓞 k) k) * x) ⁻¹' (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := by
    ext x; exact inM_iff M hM x
  have hc : Continuous (fun x : FiniteAdeleRing (𝓞 k) k =>
      (((natCast_isUnit (k := k) M hM).unit⁻¹ : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k) * x) :=
    continuous_const.mul continuous_id
  have ho : IsOpen (OH k : Set (FiniteAdeleRing (𝓞 k) k)) := GroundTheory.Global.isOpen_integralFiniteAdeles
  rw [hS]
  exact ⟨ho.preimage hc, (AddSubgroup.isClosed_of_isOpen (OH k).toAddSubgroup ho).preimage hc⟩

theorem exists_pow_lt' {c a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hc : c < 1) : ∃ n : ℕ, c ^ n < a := by
  rcases eq_or_ne c 0 with rfl | hc0
  · exact ⟨1, by simpa using (zero_lt_iff.mpr ha)⟩
  obtain ⟨α, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  obtain ⟨β, rfl⟩ := WithZero.ne_zero_iff_exists.mp ha
  have hα : Multiplicative.toAdd α < 0 := by
    have h1 : ((α : WithZero (Multiplicative ℤ))) < ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      simpa using hc
    rw [WithZero.coe_lt_coe] at h1
    exact h1
  refine ⟨(Multiplicative.toAdd β).natAbs + 1, ?_⟩
  rw [← WithZero.coe_pow, WithZero.coe_lt_coe]
  show Multiplicative.toAdd (α ^ ((Multiplicative.toAdd β).natAbs + 1)) < Multiplicative.toAdd β
  rw [toAdd_pow, nsmul_eq_mul]
  set a := Multiplicative.toAdd α
  set b := Multiplicative.toAdd β
  have ha1 : a ≤ -1 := by omega
  have h3 : (((b.natAbs + 1 : ℕ) : ℤ)) * a ≤ -(((b.natAbs + 1 : ℕ) : ℤ)) := by
    have : (0 : ℤ) ≤ ((b.natAbs + 1 : ℕ) : ℤ) := by positivity
    nlinarith
  push_cast at h3 ⊢
  have h4 := neg_abs_le b
  linarith

theorem natCast_apply' (v : HeightOneSpectrum (𝓞 k)) (M : ℕ) :
    (M : FiniteAdeleRing (𝓞 k) k) v = (M : v.adicCompletion k) := by
  rw [← map_natCast (algebraMap k (FiniteAdeleRing (𝓞 k) k)) M, FiniteAdeleRing.algebraMap_apply]
  exact map_natCast (algebraMap k (v.adicCompletion k)) M

theorem valued_natCast (v : HeightOneSpectrum (𝓞 k)) (n : ℕ) :
    Valued.v (n : v.adicCompletion k) = v.intValuation (n : 𝓞 k) := by
  have := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := k) v (n : 𝓞 k)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at this
  rw [← this]
  congr 1
  simp

theorem eq_zero_of_forall_inM (x : FiniteAdeleRing (𝓞 k) k) (hx : ∀ M : ℕ, M ≠ 0 → InM M x) : x = 0 := by
  refine Subtype.ext (funext fun v => ?_)
  change x v = 0
  by_contra hxv
  set N : ℕ := Ideal.absNorm v.asIdeal with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hNmem : (N : 𝓞 k) ∈ v.asIdeal := Ideal.absNorm_mem v.asIdeal
  have hlt : v.intValuation (N : 𝓞 k) < 1 := (v.intValuation_lt_one_iff_mem _).mpr hNmem
  have hxv0 : Valued.v (x v) ≠ 0 := by simpa using hxv
  obtain ⟨n, hn⟩ := exists_pow_lt' hxv0 hlt
  obtain ⟨y, hy, hxy⟩ := hx (N ^ n) (pow_ne_zero _ hN0)
  have hcomp : x v = ((N ^ n : ℕ) : v.adicCompletion k) * y v := by
    rw [hxy]
    have h1 := natCast_apply' v (N ^ n)
    change ((N ^ n : ℕ) : FiniteAdeleRing (𝓞 k) k) v * y v = _
    rw [h1]
  have hyv : Valued.v (y v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).mp (hy v)
  have hle : Valued.v (x v) ≤ v.intValuation (N : 𝓞 k) ^ n := by
    rw [hcomp, map_mul, valued_natCast, Nat.cast_pow, map_pow]
    exact mul_le_of_le_one_right' hyv
  exact absurd (lt_of_le_of_lt hle hn) (lt_irrefl _)

theorem inMTop : InMTop := fun k _ _ =>
  ⟨fun M hM => isOpen_isClosed M hM, fun x hx => eq_zero_of_forall_inM x hx⟩

end GlobalTheory.CompanionTheory.RgEis.InMTopPf
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField.AdeleRing Nat

namespace GlobalTheory.CompanionTheory.RgEisSupp

open PositivityTheory.RgEis PositivityTheory.RgEis.TF

theorem inM_of_dvd {k : Type} [Field k] [NumberField k] {M N : ℕ} (h : M ∣ N)
    {x : FiniteAdeleRing (𝓞 k) k} (hx : InM N x) : InM M x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨(c : FiniteAdeleRing (𝓞 k) k) * y, (OH k).mul_mem (natCast_mem _ c) hy, ?_⟩
  push_cast
  ring

theorem col_apply {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) (κ : GL ι 𝔸[k]) (r : ι) :
    TF.col i₀ κ r = ((κ⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) r i₀ := by
  rw [TF.col, Matrix.mulVec_single_one]
  rfl

theorem mem_stab_of_inv_col {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : GL ι R) (i₀ : ι) (h : ∀ j, j ≠ i₀ → ((g⁻¹ : GL ι R) : Matrix ι ι R) j i₀ = 0) :
    g ∈ stab R ({i₀} : Set ι) := by
  have key : ∀ r, (g : Matrix ι ι R) r i₀ * ((g⁻¹ : GL ι R) : Matrix ι ι R) i₀ i₀ = (1 : Matrix ι ι R) r i₀ := by
    intro r
    have e : ((g : Matrix ι ι R) * ((g⁻¹ : GL ι R) : Matrix ι ι R)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← e, Matrix.mul_apply]
    exact (Finset.sum_eq_single (f := fun m => (g : Matrix ι ι R) r m * ((g⁻¹ : GL ι R) : Matrix ι ι R) m i₀) i₀
      (fun m _ hm => by simp only [h m hm, mul_zero]) (fun hi => absurd (Finset.mem_univ _) hi)).symm
  show ∀ r ∉ ({i₀} : Set ι), ∀ c ∈ ({i₀} : Set ι),
    (g : Matrix ι ι R) r c = 0 ∧ ((g⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  obtain rfl : c = i₀ := hc
  have hr' : r ≠ c := hr
  refine ⟨?_, h r hr'⟩
  have h0 := key r
  have h1 := key c
  rw [Matrix.one_apply_ne hr'] at h0
  rw [Matrix.one_apply_eq] at h1
  calc (g : Matrix ι ι R) r c
      = (g : Matrix ι ι R) r c * ((g : Matrix ι ι R) c c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) := by rw [h1, mul_one]
    _ = ((g : Matrix ι ι R) r c * ((g⁻¹ : GL ι R) : Matrix ι ι R) c c) * (g : Matrix ι ι R) c c := by ring
    _ = 0 := by rw [h0, zero_mul]

theorem supp : ColLaw → InMTop → Supp := by
  intro hCol hTop k _ _ ι _ _ i₀ hK U hU M₀ hM₀
  obtain ⟨hmem, hcont, -, -⟩ := hCol k ι i₀
  obtain ⟨hclop, hzero⟩ := hTop k
  have : CompactSpace ((adStd k).kGL ι) := isCompact_iff_compactSpace.mp hK

  set O : Set ((adStd k).kGL ι) :=
    {κ | ∃ p : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] ({i₀} : Set ι) ∧ ∃ u ∈ interior U, κ = p * u} with hOdef
  have hO : IsOpen O := by
    have e : O = ⋃ p : {p : (adStd k).kGL ι // p.1 ∈ stab 𝔸[k] ({i₀} : Set ι)},
        (fun x => (p.1)⁻¹ * x) ⁻¹' interior U := by
      ext κ
      simp only [hOdef, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨p, hp, u, hu, rfl⟩
        exact ⟨⟨p, hp⟩, by simpa using hu⟩
      · rintro ⟨⟨p, hp⟩, h⟩
        exact ⟨p, hp, _, h, by simp⟩
    rw [e]
    exact isOpen_iUnion fun p => isOpen_interior.preimage (continuous_const.mul continuous_id)
  have hfc : Continuous fun κ : (adStd k).kGL ι => TF.col i₀ κ.1 := hcont.comp continuous_subtype_val

  set C : ℕ → Set ((adStd k).kGL ι) := fun n =>
    {κ | (∀ j, j ≠ i₀ → InM (n ! * M₀) (TF.col i₀ κ.1 j).2) ∧
      ∀ w, 1 - 1 / ((n : ℝ) + 1) ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2} with hCdef
  have hne : ∀ n : ℕ, n ! * M₀ ≠ 0 := fun n => Nat.mul_ne_zero (Nat.factorial_ne_zero n) hM₀
  have hCcl : ∀ n, IsClosed (C n) := by
    intro n
    simp only [hCdef, Set.setOf_and, Set.setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ => ?_) (isClosed_iInter fun w => ?_)
    · have c2 : Continuous fun κ : (adStd k).kGL ι => (TF.col i₀ κ.1 j).2 :=
        continuous_snd.comp ((continuous_apply j).comp hfc)
      exact (hclop _ (hne n)).2.preimage c2
    · have c1 : Continuous fun κ : (adStd k).kGL ι => ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 :=
        (((continuous_apply w).comp (continuous_fst.comp ((continuous_apply i₀).comp hfc))).norm).pow 2
      exact isClosed_le continuous_const c1
  have hanti : ∀ n, C (n + 1) ⊆ C n := by
    intro n κ hκ
    refine ⟨fun j hj => inM_of_dvd (Nat.mul_dvd_mul_right (Nat.factorial_dvd_factorial (Nat.le_succ n)) M₀) (hκ.1 j hj), fun w => ?_⟩
    refine le_trans ?_ (hκ.2 w)
    have : (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith
    linarith
  have hex : ∃ n, C n ⊆ O := by
    by_contra hno
    push_neg at hno
    obtain ⟨κ, hκ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n => C n \ O) (fun n => Set.diff_subset_diff_left (hanti n))
      (fun n => Set.nonempty_of_not_subset (hno n)) ((hCcl 0).sdiff hO).isCompact
      (fun n => (hCcl n).sdiff hO)
    have hall : ∀ n, κ ∈ C n := fun n => (Set.mem_iInter.1 hκ n).1
    have hκO : κ ∉ O := (Set.mem_iInter.1 hκ 0).2
    have hfin : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).2 = 0 := fun j hj =>
      hzero _ fun M hM => inM_of_dvd
        ((Nat.dvd_factorial (Nat.pos_of_ne_zero hM) le_rfl).mul_right M₀) ((hall M).1 j hj)
    have hone : ∀ w, 1 ≤ ‖(TF.col i₀ κ.1 i₀).1 w‖ ^ 2 := by
      intro w
      refine le_of_forall_pos_le_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hall n).2 w
      linarith
    have hinf : ∀ j, j ≠ i₀ → (TF.col i₀ κ.1 j).1 = 0 := by
      intro j hj
      funext w
      have hs := (hmem κ.1 κ.2).1 w
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)] at hs
      have hle : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤
          ∑ x ∈ Finset.univ.erase i₀, ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2 :=
        Finset.single_le_sum (f := fun x => ‖(TF.col i₀ κ.1 x).1 w‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      have h0 : ‖(TF.col i₀ κ.1 j).1 w‖ ^ 2 ≤ 0 := by
        have := hone w
        linarith
      have h1 : ‖(TF.col i₀ κ.1 j).1 w‖ = 0 := by
        have h2 := sq_nonneg ‖(TF.col i₀ κ.1 j).1 w‖
        exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 h2)
      exact norm_eq_zero.1 h1
    have hst : κ.1 ∈ stab 𝔸[k] ({i₀} : Set ι) := by
      refine mem_stab_of_inv_col κ.1 i₀ fun j hj => ?_
      rw [← col_apply]
      exact Prod.ext (hinf j hj) (hfin j hj)
    exact hκO ⟨κ, hst, 1, mem_interior_iff_mem_nhds.2 hU, (mul_one κ).symm⟩
  obtain ⟨n, hn⟩ := hex
  refine ⟨n ! * M₀, 1 / ((n : ℝ) + 1), hne n, Dvd.intro_left _ rfl, by positivity, fun κ h1 h2 => ?_⟩
  obtain ⟨p, hp, u, hu, e⟩ := hn (show κ ∈ C n from ⟨h1, fun w => (h2 w).le⟩)
  exact ⟨p, hp, u, interior_subset hu, e⟩

end GlobalTheory.CompanionTheory.RgEisSupp
end
end

section

noncomputable section

open NumberField NumberField.mixedEmbedding IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical

set_option synthInstance.maxSize 1000

namespace GlobalTheory.CompanionTheory.RgEisTF

open PositivityTheory.RgEis PositivityTheory.RgEis.TF GroundTheory.Global GroundTheory.Automorphic GroundTheory.Global.IdeleGroup

theorem zetaIntegrand_tensor {k : Type} [Field k] [NumberField k]
    (φ : 𝓢(Unit → mixedSpace k, ℂ)) (g : (Unit → FiniteAdeleRing (𝓞 k) k) → ℂ)
    (ω : HeckeCharacter k) (s : ℂ) (x : IdeleGroup k) :
    GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s =
      (rd φ (fun _ => ((toInfinite k x : (InfiniteAdeleRing k)ˣ) : InfiniteAdeleRing k)) *
          (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) *
          ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s) *
        (g (fun _ => ((toFinite k x : (FiniteAdeleRing (𝓞 k) k)ˣ) : FiniteAdeleRing (𝓞 k) k)) *
          (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
          ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s) := by
  have hchi : (ω.toIdele x : ℂ) = (ω.toIdele (ofFinite (toFinite k x)) : ℂ) *
      (ω.toIdele (ofInfinite (toInfinite k x)) : ℂ) := by
    rw [← Circle.coe_mul, ← map_mul, ofFinite_mul_ofInfinite]
  have hmod : ((ideleModule k x : ℝ) : ℂ) ^ s =
      ((ideleModule k (ofInfinite (toInfinite k x)) : ℝ) : ℂ) ^ s *
        ((ideleModule k (ofFinite (toFinite k x)) : ℝ) : ℂ) ^ s := by
    have h : (ideleModule k x : ℝ) = (ideleModule k (ofInfinite (toInfinite k x)) : ℝ) *
        (ideleModule k (ofFinite (toFinite k x)) : ℝ) := by
      conv_lhs => rw [← ofFinite_mul_ofInfinite x, map_mul]
      rw [mul_comm]
      rfl
    rw [h, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (ideleModule k _).2.le
      (ideleModule k _).2.le]
  rw [hchi, hmod]
  change φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * g (fun _ => (x : 𝔸[k]).2) * _ * _ = _
  change _ = (φ (fun _ => homeomorphMixedSpace k (x : 𝔸[k]).1) * _ * _) *
    (g (fun _ => (x : 𝔸[k]).2) * _ * _)
  ring

theorem zSplit : ZSplit := by
  intro k _ _ φ g ω s _
  set A : (InfiniteAdeleRing k)ˣ → ℂ := fun a =>
    rd φ (fun _ => (a : InfiniteAdeleRing k)) * (ω.toIdele (ofInfinite a) : ℂ) *
      ((ideleModule k (ofInfinite a) : ℝ) : ℂ) ^ s with hA
  set B : (FiniteAdeleRing (𝓞 k) k)ˣ → ℂ := fun b =>
    g (fun _ => (b : FiniteAdeleRing (𝓞 k) k)) * (ω.toIdele (ofFinite b) : ℂ) *
      ((ideleModule k (ofFinite b) : ℝ) : ℂ) ^ s with hB
  have hF : ∀ x : IdeleGroup k,
      GJMatrix.schwartzBruhatTensorPi φ g (fun _ => (x : 𝔸[k])) * (ω.toIdele x : ℂ) *
        ((ideleModule k x : ℝ) : ℂ) ^ s = (fun p => A p.1 * B p.2) (IdeleGroup.prodEquiv k x) :=
    zetaIntegrand_tensor φ g ω s
  have hemb : MeasurableEmbedding (IdeleGroup.prodEquiv k) :=
    (IdeleGroup.prodEquiv k).toHomeomorph.measurableEmbedding
  unfold globalZeta zInf zFin
  simp_rw [hF]
  rw [(measurePreserving_prodEquiv (K := k)).integral_comp hemb (fun p => A p.1 * B p.2)]
  exact integral_prod_mul A B

end GlobalTheory.CompanionTheory.RgEisTF
end
end

section

open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

theorem archExponent_eq_zero_of_mul_self {K : Type _} [Field K] [NumberField K]
    (w : InfinitePlace K) {μ : GroundTheory.Global.HeckeCharacter K} (hμ : μ * μ = 1) :
    archExponent w μ = 0 := by
  have h : archExponent w μ = -archExponent w μ := by
    rw [← archExponent_inv, ← eq_inv_of_mul_eq_one_left hμ]
  linarith

end GlobalTheory.CompanionTheory.EisRk1
end
