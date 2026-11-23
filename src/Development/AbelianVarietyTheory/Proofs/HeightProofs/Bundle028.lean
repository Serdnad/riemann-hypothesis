module

public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Formalism.SharpRestriction.Divisibility.WeightFamilies
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_adelic_lattice_iff_local_selfDual_completion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (V : HSpace E) (y : Fin V.rank → Af F ⊗[F] E), y ∈ Formalism.MainNotions.StandardLattice.latHat F E {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ V.L0} ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F E) (y i)) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
  first | exact @GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | exact GlobalTheory.LatticeLocalGlobal.mem_latHat_iff | (intros; apply GlobalTheory.LatticeLocalGlobal.mem_latHat_iff <;> assumption)
end

section

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.RunJoin.Inh
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num GlobalTheory.RunJoin

theorem nums {A k b s PP TO rd r d q fm : ℝ} (h : Bs A k b s PP TO rd) (hr0 : 0 ≤ r) (hr : r ≤ A) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * A * b) (hq : (k * b) ^ 8 ≤ q) (hf0 : 0 ≤ fm) (hf : fm ≤ k ^ 4) :
    (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ q ∧ TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 ≤ q ∧
      2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ q := by
  have hs : (10 : ℝ) ^ 100 ≤ s := h.sb_ge
  have hs1 : (40000 : ℝ) ≤ s := le_trans (by norm_num) hs
  have hk : (1 : ℝ) ≤ k := by linarith [h.k8]
  have hR : rd ^ 7 ≤ s := h.rd_pow_le (by norm_num)
  have hR0 : 0 ≤ rd ^ 7 := by have := h.rd1; positivity
  have hP0 : 0 ≤ PP := le_trans (by positivity) h.PP_ge
  have hP := h.PP_le_sb
  have hP3 := h.param_cube_le_bound
  have hTP := h.hTP
  have hT0 : 0 ≤ TO := by linarith [h.one_le_order_alt]
  have hb : b = s ^ 2 := by rw [← h.sb_sq]; ring
  have hd' : d ≤ 4 * k ^ 2 * s ^ 2 := by
    have := h.Ak
    rw [hb] at hd
    have : A * s ^ 2 ≤ 2 * k ^ 2 * s ^ 2 := by gcongr
    linarith
  have hq' : k ^ 8 * s ^ 16 ≤ q := by rw [hb] at hq; calc k ^ 8 * s ^ 16 = (k * s ^ 2) ^ 8 := by ring
    _ ≤ q := hq
  have hr' : r ≤ 2 * k ^ 2 := hr.trans h.Ak
  have key : ∀ (a c : ℕ) (C : ℝ), a ≤ 8 → c ≤ 15 → 0 ≤ C → C ≤ 40000 → C * (k ^ a * s ^ c) ≤ q := by
    intro a c C ha hc hC0 hC
    have e1 : k ^ a ≤ k ^ 8 := pow_le_pow_right₀ hk ha
    have e2 : s ^ c ≤ s ^ 15 := pow_le_pow_right₀ (by linarith) hc
    calc C * (k ^ a * s ^ c) ≤ s * (k ^ 8 * s ^ 15) := by gcongr; linarith
      _ = k ^ 8 * s ^ 16 := by ring
      _ ≤ q := hq'
  refine ⟨?_, ?_, ?_⟩
  · calc (rd ^ 7) ^ 4 * PP ^ 3 * d ^ 2 ≤ s ^ 4 * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 16 * (k ^ 4 * s ^ 9) := by ring
      _ ≤ q := key 4 9 16 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc TO * (1250 * r) * rd ^ 7 * PP * d ^ 2 = (TO * PP) * (1250 * r) * rd ^ 7 * d ^ 2 := by ring
      _ ≤ s * (1250 * (2 * k ^ 2)) * s * (4 * k ^ 2 * s ^ 2) ^ 2 := by gcongr
      _ = 40000 * (k ^ 6 * s ^ 6) := by ring
      _ ≤ q := key 6 6 40000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · calc 2 * (fm * (rd ^ 7) ^ 2 * (rd ^ 7 * PP * d ^ 2)) ≤ 2 * (k ^ 4 * s ^ 2 * (s * s * (4 * k ^ 2 * s ^ 2) ^ 2)) := by gcongr
      _ = 32 * (k ^ 8 * s ^ 8) := by ring
      _ ≤ q := key 8 8 32 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem eRR7 : WeightFamilies.RRv D 7 = D.host.rdE ^ 7 := by
  unfold WeightFamilies.RRv; exact_mod_cast Real.rpow_natCast D.host.rdE 7

end GlobalTheory.RunJoin.Inh
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.OrdVal

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem nonneg_of_isIntegral (u : AddValuation A (WithTop ℤ))
    (hu : ∀ r : O, 0 ≤ u (algebraMap O A r)) {x : A} (hx : IsIntegral O x) : 0 ≤ u x := by
  let v : Valuation A (Multiplicative (WithTop ℤ)ᵒᵈ) := u
  let f : O →+* v.integer := (algebraMap O A).codRestrict v.integer (fun r => hu r)
  have h1 : IsIntegral v.integer x := by
    obtain ⟨p, hp, hz⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hz
  exact (Valuation.integer.integers v).mem_of_integral h1

def centre (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    Ideal ↥(As O A) where
  carrier := {a | 0 < u (a : A)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) b
    exact lt_of_lt_of_le (lt_min ha hb) this
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * a)
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (hu c))

theorem centre_isPrime (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    (centre u hu).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} h => ?_⟩
  · have : (1 : ↥(As O A)) ∈ centre u hu := h ▸ Submodule.mem_top
    change 0 < u (1 : A) at this
    simp at this
  · change 0 < u ((a : A) * b) at h
    by_contra hn
    rw [not_or] at hn
    have ha : u (a : A) = 0 := le_antisymm (not_lt.1 hn.1) (hu a)
    have hb : u (b : A) = 0 := le_antisymm (not_lt.1 hn.2) (hu b)
    rw [u.map_mul, ha, hb] at h
    simp at h

theorem centre_isMaximal (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    {ϖ : O} (hϖ : Irreducible ϖ) (hpos : 0 < u (algebraMap O A ϖ)) :
    (centre u hu).IsMaximal := by
  haveI := centre_isPrime u hu
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) _ ?_
  have hle : IsLocalRing.maximalIdeal O ≤ (centre u hu).comap (algebraMap O ↥(As O A)) := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hpos
  have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  change ((centre u hu).comap (algebraMap O ↥(As O A))).IsMaximal
  rw [← this]
  infer_instance

theorem le_of_vL_le (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    (ζ : Pts O A) [IsDVRAt ζ] (hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0)
    {a b : ↥(As O A)} (hab : vL ζ a ≤ vL ζ b) : u (a : A) ≤ u (b : A) := by
  rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
  obtain ⟨z, hz⟩ := hab
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl z
  have h1 : algebraMap _ (Loc ζ) (b * s) = algebraMap _ (Loc ζ) (a * x) := by
    simp only at hs
    rw [map_mul, map_mul, hz, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h1
  have h2 : ((c : ↥(As O A)) : A) * ((b : A) * ((s : ↥(As O A)) : A))
      = ((c : ↥(As O A)) : A) * ((a : A) * (x : A)) := congrArg Subtype.val hc
  have h3 := congrArg u h2
  rw [u.map_mul, u.map_mul, u.map_mul, u.map_mul, hζ _ c.2, hζ _ s.2, zero_add, zero_add,
    add_zero] at h3
  rw [h3]
  exact le_add_of_nonneg_right (hu x)

theorem exists_vL_eq_one (ζ : Pts O A) [IsDVRAt ζ] : ∃ a : ↥(As O A), vL ζ a = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl π
  refine ⟨x, ?_⟩
  have h0 := (vL_eq_zero_iff ζ s).2 s.2
  rw [vL_eq_addVal] at h0
  simp only at hs
  rw [vL_eq_addVal, ← hs, IsDiscreteValuationRing.addVal_mul, h0,
    IsDiscreteValuationRing.addVal_uniformizer hπ, add_zero]

theorem exists_ord_eq [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ)
    (u : AddValuation A (WithTop ℤ)) (hO : ∀ r : O, 0 ≤ u (algebraMap O A r))
    (hpos : 0 < u (algebraMap O A ϖ)) (hone : ∃ a, u a = 1) :
    ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a := by
  have hu : ∀ a : ↥(As O A), 0 ≤ u (a : A) := fun a => nonneg_of_isIntegral u hO a.2
  let ζ : Pts O A := ⟨centre u hu, centre_isMaximal u hu h.irreducible hpos⟩
  have hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0 :=
    fun a ha => le_antisymm (not_lt.1 ha) (hu a)
  obtain ⟨a₀, ha₀⟩ := exists_vL_eq_one ζ
  have hfin : ∀ (b : ↥(As O A)) (m : ℕ), vL ζ b = m → u (b : A) = m • u (a₀ : A) := by
    intro b m hb
    have e : vL ζ (a₀ ^ m) = vL ζ b := by rw [vL_pow, ha₀, hb]; simp
    have := le_antisymm (le_of_vL_le u hu ζ hζ e.ge) (le_of_vL_le u hu ζ hζ e.le)
    rw [this, SubmonoidClass.coe_pow, u.map_pow]
  have htop : ∀ b : ↥(As O A), vL ζ b = ⊤ → u (b : A) = ⊤ := by
    intro b hb
    have := le_of_vL_le u hu ζ hζ (a := 0) (b := b) (by rw [hb]; exact le_top)
    simpa using this
  have hϖ : u (algebraMap O A ϖ) = ep ϖ ζ • u (a₀ : A) :=
    hfin (algebraMap O ↥(As O A) ϖ) _ (coe_ep ζ h).symm
  have hϖfin : u (algebraMap O A ϖ) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := h.isUnit.exists_right_inv
    intro ht
    have := congrArg u hy
    rw [u.map_mul, ht, u.map_one] at this
    simp at this
  have ha₀fin : u (a₀ : A) ≠ ⊤ := by
    intro ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖ, ht, hk, succ_nsmul] at hϖfin
    simp at hϖfin
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ha₀fin
  have hq0 : 0 ≤ q := by
    have := hu a₀
    rw [← hq] at this
    exact_mod_cast this
  have key : ∀ x : A, (Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ k : ℤ, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = (k : WithTop ℤ) ∧ u x = ((k * q : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨n, hn⟩ := h.denom x
    have e1 : u (ϖ ^ n • x) = ((n * (ep ϖ ζ * q) : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖ, ← hq, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    rw [ord_eq ζ h hn, ordAt]
    cases hv : vL ζ ⟨ϖ ^ n • x, hn⟩ with
    | top =>
      left
      refine ⟨by simp, ?_⟩
      have := htop _ hv
      change u (ϖ ^ n • x) = ⊤ at this
      rw [e1, WithTop.add_eq_top] at this
      exact this.resolve_left WithTop.coe_ne_top
    | coe m =>
      right
      refine ⟨m + -(n * ep ϖ ζ), by rw [ENat.map_natCast, ← WithTop.coe_add], ?_⟩
      have := hfin _ m hv
      change u (ϖ ^ n • x) = _ at this
      rw [e1, ← hq, ← WithTop.coe_nsmul, nsmul_eq_mul] at this
      have hx : u x ≠ ⊤ := by
        intro ht
        rw [ht, add_top] at this
        exact WithTop.top_ne_coe this
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at this
      rw [← ht, WithTop.coe_inj]
      linarith
  have hq1 : q = 1 := by
    obtain ⟨a, ha⟩ := hone
    rcases key a with ⟨_, h2⟩ | ⟨k, _, h2⟩
    · rw [ha] at h2
      exact absurd h2 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h2
      exact Int.eq_one_of_mul_eq_one_left hq0 h2.symm
  refine ⟨ζ, fun a => ?_⟩
  rcases key a with ⟨h1, h2⟩ | ⟨k, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hq1, mul_one]

theorem eq_zero_of_ord_eq_top [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ) (a : A)
    (ha : ∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) : a = 0 := by
  obtain ⟨n, hn⟩ := h.denom a
  have key : (⟨ϖ ^ n • a, hn⟩ : ↥(As O A)) ∈ (⊥ : Ideal ↥(As O A)) := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • a, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ)) ⊥ := by
      intro ζ
      have h1 := ha ζ
      rw [ord_eq ζ h hn, ordAt, WithTop.add_eq_top] at h1
      have h2 : vL ζ ⟨ϖ ^ n • a, hn⟩ = ⊤ := by
        simpa using h1.resolve_right WithTop.coe_ne_top
      rw [(vL_eq_top_iff ζ _).1 h2]
      exact Submodule.zero_mem _
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  have h2 : ϖ ^ n • a = 0 := congrArg Subtype.val (Ideal.mem_bot.1 key)
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

theorem valuation_eq_ord_and_eq_zero :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [∀ ζ : Pts O A, IsDVRAt ζ] (ϖ : O), IsUnif A ϖ → (∀ u : AddValuation A (WithTop ℤ), (∀ r : O, 0 ≤ u (algebraMap O A r)) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a) ∧ ∀ a : A, (∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) → a = 0 :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨exists_ord_eq h, eq_zero_of_ord_eq_top h⟩

end GlobalTheory.OrdVal
end
