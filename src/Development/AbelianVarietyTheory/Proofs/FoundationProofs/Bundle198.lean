module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle090
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle089
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle190
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
public import Mathlib.NumberTheory.ModularForms.Petersson
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle007
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralTateInertiaCyclotomicTwistTorsion
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerParameterPowersOrthogonalGeometricInvariant
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle193
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
public import Mathlib.NumberTheory.LSeries.Dirichlet
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_sat : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T a b M hM ha hb hb0 hinv ⟨P, hP, hPe⟩
  obtain ⟨_, hMD, hAE, _, hmemHs⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  obtain ⟨hNT, hid, hunit⟩ := GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units
  obtain ⟨hmapsto, _, _, hmobSL, hmobD, _⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨p, u, hu, hpn, hp⟩ := GlobalTheory.T.modularFunctionFractionField_clear_denominators Ω ε T P hP
  set n := P.natDegree with hn
  have hR : ∀ i, InR ε.range (p i : ℍ → ℂ) := fun i => ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 _).1 (p i).2
  have hpD : ∀ i, DifferentiableOn ℂ (up (p i : ℍ → ℂ)) Hs := fun i => (hMD _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hR i))

  have hup : ∀ (g : ℂ → ℂ) (z : ℂ), z ∈ Hs → up (fun τ : ℍ => g τ) z = g z := by
    intro g z hz
    simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
  have hupT : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp [up]

  have hxb : (((a / b : ℂ → ℂ)) : Mero) * (b : Mero) = (a : Mero) := by
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    filter_upwards [(hunit b hb hb0).1] with z hz
    simp [div_mul_cancel₀ _ hz]

  have hsum : ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i = 0 := by
    calc _ = T.an u * P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) := by
          rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hp i, map_mul, mul_assoc]
      _ = 0 := by rw [hPe, mul_zero]
  set F : ℂ → ℂ := fun z => ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) z * a z ^ i * b z ^ (n - i) with hF
  have e2 : F = ∑ i ∈ Finset.range (n + 1), up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) := by
    funext z; simp [hF, Finset.sum_apply]
  have hFg : (F : Mero) = 0 := by
    have e1 : (F : Mero) = Filter.Germ.coeRingHom _ F := rfl

    rw [e1, e2, map_sum]
    change ∑ i ∈ _, ((up (p i : ℍ → ℂ) * a ^ i * b ^ (n - i) : ℂ → ℂ) : Mero) = _
    simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
    calc _ = (b : Mero) ^ n * ∑ i ∈ Finset.range (n + 1), T.an (T.io (p i)) * (((a / b : ℂ → ℂ)) : Mero) ^ i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
          rw [T.an_io, ← hxb]
          show (up (p i : ℍ → ℂ) : Mero) * _ * _ = _ * ((up (p i : ℍ → ℂ) : Mero) * _)
          rw [mul_pow, mul_assoc, mul_assoc, ← pow_mul_pow_sub (b : Mero) hin]
          ring
      _ = 0 := by rw [hsum, mul_zero]
  have hFD : DifferentiableOn ℂ F Hs := by
    rw [e2]
    refine DifferentiableOn.sum fun i _ => ?_
    exact ((hpD i).mul (ha.pow i)).mul (hb.pow (n - i))
  have hF0 : ∀ z ∈ Hs, F z = 0 := by
    have := hid F (fun _ => 0) hFD (differentiableOn_const 0) (by rw [hFg]; rfl)
    exact this

  have haM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => a τ) := (hMD _).2 (ha.congr fun z hz => hup a z hz)
  have hbM : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => b τ) := (hMD _).2 (hb.congr fun z hz => hup b z hz)
  have hbne : (fun τ : ℍ => b τ) ≠ 0 := by
    intro h0
    apply hb0
    have : (b : Mero) = ((0 : ℂ → ℂ) : Mero) := hAE b 0 fun z hz => by
      simpa using congrFun h0 ⟨z, hz⟩
    rw [this]; rfl
  have hinvT : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a ((γ • τ : ℍ) : ℂ) * b τ = a τ * b ((γ • τ : ℍ) : ℂ) := by
    intro γ hγ τ
    have hmD : DifferentiableOn ℂ (mob (ofSL γ)) Hs := hmobD _
    have hmap : Set.MapsTo (mob (ofSL γ)) Hs Hs := fun z hz => hmapsto _ z hz
    have h1 : DifferentiableOn ℂ (fun z => a (mob (ofSL γ) z) * b z) Hs := (ha.comp hmD hmap).mul hb
    have h2 : DifferentiableOn ℂ (fun z => a z * b (mob (ofSL γ) z)) Hs := ha.mul (hb.comp hmD hmap)
    have := hid _ _ h1 h2 (hinv γ hγ) τ (hmemHs τ)
    simpa [hmobSL] using this
  have hpn' : (p n : ℍ → ℂ) ≠ 0 := by
    intro h0; apply hpn; ext1; exact h0
  have hsumT : ∀ τ : ℍ, ∑ i ∈ Finset.range (n + 1), (p i : ℍ → ℂ) τ * (fun τ : ℍ => a τ) τ ^ i * (fun τ : ℍ => b τ) τ ^ (n - i) = 0 := by
    intro τ
    have := hF0 τ (hmemHs τ)
    simpa [hF, hupT] using this
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed (R := ℚ)
  obtain ⟨h, hhR, hh⟩ := GlobalTheory.T.saturation_levelFunctions_integralRelation Ω ε M n (fun τ : ℍ => a τ) (fun τ : ℍ => b τ) (fun i => (p i : ℍ → ℂ)) hM haM hbM hbne
    hinvT hR hpn' hsumT
  let hr : ring ε.range := ⟨h, mem_ring_of_inR hhR⟩
  have hio0 : T.io (p n) ≠ 0 := by
    intro h0; apply hpn; exact T.io_inj (by rw [h0, map_zero])
  refine ⟨T.io hr / T.io (p n), ?_⟩
  have hg0 : (up (p n : ℍ → ℂ) : Mero) ≠ 0 := by
    intro h0
    have hinj : Function.Injective T.an := T.an.injective
    apply hio0; apply hinj; rw [map_zero, T.an_io]; exact h0
  have hU : IsUnit (up (p n : ℍ → ℂ) : Mero) := (hunit _ (hpD n) hg0).2
  have hrel : (up (p n : ℍ → ℂ) : Mero) * (a : Mero) = (up h : Mero) * (b : Mero) := by
    rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_mul]
    refine hAE _ _ fun z hz => ?_
    have e := hh ⟨z, hz⟩
    simp only [Pi.mul_apply]
    have q1 : up (p n : ℍ → ℂ) z = (p n : ℍ → ℂ) ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    have q2 : up h z = h ⟨z, hz⟩ := by
      simp [up, UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    rw [q1, q2]; simpa using e
  have hf : T.an (T.io hr / T.io (p n)) * (up (p n : ℍ → ℂ) : Mero) = (up h : Mero) := by
    have : T.io hr / T.io (p n) * T.io (p n) = T.io hr := div_mul_cancel₀ _ hio0
    have := congrArg T.an this
    rw [map_mul, T.an_io, T.an_io] at this
    exact this
  apply hU.mul_left_cancel
  rw [hrel, ← hf]; ring

end GlobalTheory
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem GlobalTheory.EisM.hsum_inv_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  intro k L L' N ε Δ ι _ β f hk hNL hNL' hΔ hΔγ hβ hf
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (hsum k (ch ε) β f) hk).2.2.1 L' (ch ε)]
  intro γ hγ
  have hNγ : (N : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hNL').trans hγ
  have hβmem : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  have hγγ : (γ : M2) * ((γ⁻¹ : SL(2,ℤ)) : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγγ' : ((γ⁻¹ : SL(2,ℤ)) : M2) * (γ : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγinv : (L' : ℤ) ∣ (γ⁻¹ : SL(2,ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ.neg_right
  set β' : ι → M2 := fun i => β i * (γ : M2) with hβ'
  have hβ'rep : LRep L Δ β' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨g, i⟩ -
      have := hβ.mapsTo (Set.mem_univ (g, i))
      simp only [β', ← mul_assoc]
      exact hΔγ _ this γ hγ
    · rintro ⟨g, i⟩ - ⟨g', j⟩ - h
      have h' := congrArg (· * ((γ⁻¹ : SL(2,ℤ)) : M2)) h
      simp only [β', mul_assoc, hγγ, mul_one] at h'
      exact hβ.injOn (Set.mem_univ _) (Set.mem_univ _) h'
    · intro δ hδ
      have h1 := hΔγ δ hδ γ⁻¹ hγinv
      obtain ⟨⟨g, i⟩, -, hgi⟩ := hβ.surjOn h1
      refine ⟨(g, i), Set.mem_univ _, ?_⟩
      simp only at hgi ⊢
      rw [← mul_assoc, hgi, mul_assoc, hγγ', mul_one]
  have hsumeq := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k L N ε Δ ι ι β β' f hk hNL hΔ hβ hβ'rep hf
  have hdetγ : (0 : ℤ) < (γ : M2).det := by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  have hch : ∀ i, ch ε (β' i 0 0) = ch ε (β i 0 0) * ch ε (γ 0 0) := by
    intro i
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    simp only [ch, β', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hz, mul_zero, add_zero, map_mul]
  have hγd : ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    have h2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) hd
      push_cast at this
      rw [hz, mul_zero, sub_zero] at this
      exact this
    simp only [ch]
    rw [← map_mul, h2, map_one]
  funext τ
  have hlin : slz k (γ : M2) (hsum k (ch ε) β f) τ = ∑ i, ch ε (β i 0 0) * slz k (γ : M2) (slz k (β i) f) τ := by
    simp only [slz, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsumeq]
  simp only [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoc (β i) γ (hΔ _ (hβmem i)).1 hdetγ, hch i]
  calc ch ε (β i 0 0) * slz k (β i * ↑γ) f τ
      = ch ε (β i 0 0) * (ch ε (γ 0 0) * ch ε (γ 1 1)) * slz k (β i * ↑γ) f τ := by rw [hγd, mul_one]
    _ = _ := by simp only [β']; ring
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.GcdOut

abbrev CopVec (L : ℕ) : Type := {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}

def scl (L : ℕ) (p : ℕ+ × CopVec L) : ℤ × ℤ := (((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2)

lemma scl_injective (L : ℕ) : Function.Injective (scl L) := by
  rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩ ⟨δ', ⟨⟨a', b'⟩, hab', ha'⟩⟩ h
  simp only [scl, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab
  have g2 : Int.gcd a' b' = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab'
  have hd : (δ : ℕ) = (δ' : ℕ) := by
    have e1 := Int.gcd_mul_left ((δ : ℕ) : ℤ) a b
    have e2 := Int.gcd_mul_left ((δ' : ℕ) : ℤ) a' b'
    rw [h1, h2, e2, g1, g2] at e1
    simpa using e1.symm
  have hδ : δ = δ' := PNat.coe_injective hd
  subst hδ
  have hne : ((δ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast δ.ne_zero
  have := mul_left_cancel₀ hne h1
  have := mul_left_cancel₀ hne h2
  subst_vars
  rfl

lemma trm_zero (j : ℕ) (s : ℝ) (hj : 2 ≤ j) : trm j s 0 = 0 := by
  simp [trm, zero_pow (by omega : j ≠ 0)]

lemma trm_smul (j : ℕ) (s : ℝ) (δ : ℕ) (z : ℂ) :
    trm j s ((δ : ℂ) * z) = (((δ : ℂ) ^ j)⁻¹ * ((((δ : ℝ) ^ (2 * s))⁻¹ : ℝ) : ℂ)) * trm j s z := by
  unfold trm
  rw [norm_mul, Complex.norm_natCast, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), neg_mul,
    Real.rpow_neg (Nat.cast_nonneg _), ← neg_mul, mul_pow, mul_inv]
  push_cast
  ring

lemma cpow_split (j : ℕ) (s : ℝ) (δ : ℕ) (hδ : 0 < δ) :
    (δ : ℂ) ^ ((j : ℂ) + 2 * (s : ℂ)) = (δ : ℂ) ^ j * ((((δ : ℝ) ^ (2 * s)) : ℝ) : ℂ) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hδ.ne'), Complex.cpow_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.EisM.GcdOut

open GlobalTheory.EisM.GcdOut in
theorem GlobalTheory.EisM.lattice_sum_gcd_out (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ)
    (hj : 2 ≤ j) (hs : 0 < s) (hL : 0 < L) :
    ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) =
      LSeries (fun n => φ n) (j + 2 * s) *
        ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1},
          φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  let F : ℤ × ℤ → ℂ := fun x => latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2)
  let f : ℕ+ → ℂ := fun δ => LSeries.term (fun n => φ n) ((j : ℂ) + 2 * (s : ℂ)) (δ : ℕ)
  let g : CopVec L → ℂ := fun x => φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2)
  change ∑' x, F x = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) * ∑' x, g x
  have hsumT := (GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills j L s 0 0 τ hj hs hL ⟨0, by simp⟩ (fun x => by simp [Kills])).1
  have hgs : Summable fun x => ‖g x‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hsumT.comp_injective Subtype.val_injective)
    simp only [g, Function.comp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hLS : LSeriesSummable (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    rw [DirichletCharacter.LSeriesSummable_iff hL.ne']
    have : (2:ℝ) ≤ j := by exact_mod_cast hj
    simp
    linarith
  have hfs : Summable fun δ => ‖f δ‖ :=
    (summable_norm_iff.2 hLS).comp_injective PNat.coe_injective
  have hterm : ∀ p : ℕ+ × CopVec L, F (scl L p) = f p.1 * g p.2 := by
    rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩
    have hδ : 0 < (δ : ℕ) := δ.pos
    simp only [F, f, g, scl, latF]
    rw [if_pos (dvd_mul_of_dvd_right ha _), LSeries.term_of_ne_zero hδ.ne', cpow_split j s _ hδ]
    have e : ((((δ : ℕ) : ℤ) * a : ℤ) : ℂ) * (τ : ℂ) + ((((δ : ℕ) : ℤ) * b : ℤ) : ℂ)
        = ((δ : ℕ) : ℂ) * ((a : ℂ) * τ + b) := by push_cast; ring
    rw [e, trm_smul]
    have e2 : (((((δ : ℕ) : ℤ) * b : ℤ)) : ZMod L) = ((δ : ℕ) : ZMod L) * (b : ZMod L) := by push_cast; ring
    rw [e2, map_mul]
    have h1 : ((δ:ℕ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
    have h2 : ((((δ : ℕ) : ℝ) ^ (2 * s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _).ne'
    push_cast
    field_simp
  have hsupp : Function.support F ⊆ Set.range (scl L) := by
    rintro ⟨x1, x2⟩ hx
    simp only [Function.mem_support, F, latF] at hx
    by_cases hL1 : (L : ℤ) ∣ x1
    swap
    · simp [hL1] at hx
    rw [if_pos hL1, one_mul] at hx
    have hφ : φ (x2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hx
    have ht : trm j s ((x1 : ℂ) * τ + x2) ≠ 0 := right_ne_zero_of_mul hx
    have hgpos : 0 < Int.gcd x1 x2 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [trm_zero j s hj] at ht
    obtain ⟨a, b, hab, h1, h2⟩ := Int.exists_gcd_one hgpos
    generalize Int.gcd x1 x2 = d at h1 h2 hgpos
    have hunit : IsUnit (x2 : ZMod L) := by
      by_contra h
      exact hφ (MulChar.map_nonunit φ h)
    have hdu : IsUnit ((d : ℕ) : ZMod L) := by
      rw [h2] at hunit
      push_cast at hunit
      exact isUnit_of_mul_isUnit_right hunit
    have hcop : Nat.Coprime d L := (ZMod.isUnit_iff_coprime d L).1 hdu
    have hLa : (L : ℤ) ∣ a := by
      have hc : IsCoprime (L : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
      rw [h1] at hL1
      exact hc.dvd_of_dvd_mul_right hL1
    refine ⟨(⟨d, hgpos⟩, ⟨(a, b), Int.isCoprime_iff_gcd_eq_one.2 hab, hLa⟩), ?_⟩
    simp only [scl, PNat.mk_coe]
    rw [h1, h2, mul_comm a, mul_comm b]
  have hLser : ∑' δ : ℕ+, f δ = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    unfold LSeries
    refine (PNat.coe_injective.tsum_eq (f := LSeries.term (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ))) ?_)
    intro n hn
    have : n ≠ 0 := by
      rintro rfl
      exact hn (LSeries.term_zero _ _)
    exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩
  calc ∑' x, F x = ∑' p, F (scl L p) := ((scl_injective L).tsum_eq hsupp).symm
    _ = ∑' p : ℕ+ × CopVec L, f p.1 * g p.2 := tsum_congr hterm
    _ = (∑' δ, f δ) * ∑' x, g x := (tsum_mul_tsum_of_summable_norm hfs hgs).symm
    _ = _ := by rw [hLser]
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

lemma norm_petersson_self (k : ℕ) (h : ℍ → ℂ) (z : ℍ) :
    ‖petersson (k : ℤ) h h z‖ = ‖h z‖ ^ 2 * z.im ^ k := by
  simp only [petersson, norm_mul, Complex.norm_conj, zpow_natCast, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos z.im_pos]
  ring

lemma isZeroAtImInfty_of_bound (k : ℕ) (hk : 1 ≤ k) (h : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖h τ‖ ^ 2 * τ.im ^ k ≤ C) : IsZeroAtImInfty h := by
  rw [IsZeroAtImInfty, ZeroAtFilter, tendsto_zero_iff_norm_tendsto_zero]
  have him : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  have hsq : Tendsto (fun τ : ℍ => ‖h τ‖ ^ 2) atImInfty (𝓝 0) := by
    have hlim : Tendsto (fun τ : ℍ => max C 0 * (τ.im)⁻¹) atImInfty (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp him).const_mul (max C 0)
    refine squeeze_zero' (Eventually.of_forall fun τ => by positivity) ?_ hlim
    filter_upwards [him.eventually_ge_atTop 1] with τ hτ
    have hpos : 0 < τ.im := τ.im_pos
    have hpow : τ.im ≤ τ.im ^ k := by
      calc τ.im = τ.im ^ 1 := (pow_one _).symm
        _ ≤ τ.im ^ k := pow_le_pow_right₀ hτ hk
    rw [le_mul_inv_iff₀ hpos]
    calc ‖h τ‖ ^ 2 * τ.im ≤ ‖h τ‖ ^ 2 * τ.im ^ k :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ C := hC τ
      _ ≤ max C 0 := le_max_left _ _
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

end GlobalTheory.EisM

theorem GlobalTheory.EisM.cuspForm_of_CF : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    CF k L (ch ε) a → ∃ f : CuspForm (Gamma1 L) (k : ℤ), ⇑f = qs a := by
  intro k L N ε a hk hL hNL hcf
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨f, hf⟩ := GlobalTheory.T.modularForm_gammaOne_of_coeffSeq k L N ε a hL hNL hcf.1
  obtain ⟨C, hC⟩ := hcf.2
  have hall : ∀ γ : SL(2, ℤ), IsZeroAtImInfty ((f : ℍ → ℂ) ∣[(k : ℤ)] γ) := by
    intro γ
    refine isZeroAtImInfty_of_bound k hk _ C fun τ => ?_
    have h1 := congrArg norm (petersson_slash_SL (k : ℤ) (f : ℍ → ℂ) f γ τ)
    rw [norm_petersson_self, norm_petersson_self, hf] at h1
    rw [hf, h1]
    exact hC _
  refine ⟨⟨f.toSlashInvariantForm, f.holo', ?_⟩, hf⟩
  intro c hc
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
  intro γ _
  exact hall γ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

theorem _root_.GlobalTheory.T.integral_tate_inertia_cyclotomic_twist_torsion : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 →
  ∀ (j : ℕ), 1 ≤ j → ∀ F : Finset Ω, ∃ c : ℕ, ∀ (n : ℕ) (x : Ω), x ∈ A →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) → CgA A l n (s x) ((((cycMod ℚ Ω l n s : ZMod (l ^ n)).val : ℕ) : Ω) ^ j * x)) →
  CgA A l n ((l : Ω) ^ c * x) 0 := by
  first | exact @GlobalTheory.IntTate.integral_tate_inertia | exact GlobalTheory.IntTate.integral_tate_inertia | (intros; apply GlobalTheory.IntTate.integral_tate_inertia <;> assumption)
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.OrthDecomp

theorem orth : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo (p := p) Ω, g (c j) = c j) →
      IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) →
        ∀ j < p ^ N, IsInt (p := p) (c j) :=
  GlobalTheory.K5.Orth.orth

end GlobalTheory.K5.OrthDecomp
end

section


theorem _root_.GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  first | exact @GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | exact GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | (intros; apply GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq <;> assumption)
end
