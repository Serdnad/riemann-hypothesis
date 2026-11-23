module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Formalism.RealPlaceAnalysis.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle236
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Mathlib.FieldTheory.IsSepClosed
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle235
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle237
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import GroundTheory.LocalFields.Bundle001
import GroundTheory.LocalFields.FormalGroups.Bundle001
import GroundTheory.PAdicHodge.Bundle004
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.RgEisDGood

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem gauss_bound (b c : ℝ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3 ≤ M := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = max |b| |c| := ⟨_, rfl⟩
  have hbB : |b| ≤ B := hB ▸ le_max_left _ _
  have hcB : |c| ≤ B := hB ▸ le_max_right _ _
  have hB0 : 0 ≤ B := (abs_nonneg b).trans hbB
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 + B := ⟨_, rfl⟩
  have hT : 1 ≤ T := by linarith
  refine ⟨16 * T ^ 4 * Real.exp (B ^ 2), by positivity, fun z h1 h2 => ?_⟩
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = z.re := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = z.im := ⟨_, rfl⟩
  have hx : |x| ≤ B := by
    rw [abs_le]
    constructor
    · have := neg_abs_le b
      rw [hxdef]; linarith
    · have := le_abs_self c
      rw [hxdef]; linarith
  have hx2 : x ^ 2 ≤ B ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 2
    rwa [sq_abs] at this
  have hnorm : ‖Complex.exp (z ^ 2)‖ = Real.exp (x ^ 2 - y ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, hxdef, hydef]
  have hz : ‖z‖ ≤ |x| + |y| := by
    rw [hxdef, hydef]; exact Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = T + |y| := ⟨_, rfl⟩
  have hy0 := abs_nonneg y
  have hu1 : 1 ≤ u := by linarith
  have h1z : 1 + ‖z‖ ≤ u := by linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp (y ^ 2 / 2) := ⟨_, rfl⟩
  have hE0 : 0 < E := hEdef ▸ Real.exp_pos _
  have hE : 1 + y ^ 2 / 2 ≤ E := by
    have := Real.add_one_le_exp (y ^ 2 / 2)
    rw [hEdef]; linarith
  have hEE : E ^ 2 = Real.exp (y ^ 2) := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hu2 : u ^ 2 ≤ 4 * T ^ 2 * E := by
    have hsq : |y| ^ 2 = y ^ 2 := sq_abs y
    have hA : u ^ 2 ≤ 2 * T ^ 2 + 2 * y ^ 2 := by
      rw [hudef]
      nlinarith [sq_nonneg (T - |y|)]
    have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT
    have hC : 2 * T ^ 2 + 2 * y ^ 2 ≤ 4 * T ^ 2 * (1 + y ^ 2 / 2) := by
      nlinarith [mul_nonneg (sq_nonneg y) (sub_nonneg.2 hT2), sq_nonneg T]
    have hD : 4 * T ^ 2 * (1 + y ^ 2 / 2) ≤ 4 * T ^ 2 * E :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    linarith
  have hu4 : u ^ 4 ≤ 16 * T ^ 4 * Real.exp (y ^ 2) := by
    have h := pow_le_pow_left₀ (by positivity) hu2 2
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ ≤ (4 * T ^ 2 * E) ^ 2 := h
      _ = 16 * T ^ 4 * E ^ 2 := by ring
      _ = 16 * T ^ 4 * Real.exp (y ^ 2) := by rw [hEE]
  have hz3 : (1 + ‖z‖) ^ 3 ≤ u ^ 4 := by
    have h0 : 0 ≤ 1 + ‖z‖ := by positivity
    calc (1 + ‖z‖) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ h0 h1z 3
      _ ≤ u ^ 4 := pow_le_pow_right₀ hu1 (by norm_num)
  have hexp : Real.exp (x ^ 2 - y ^ 2) ≤ Real.exp (B ^ 2) * Real.exp (-y ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  rw [hnorm]
  calc Real.exp (x ^ 2 - y ^ 2) * (1 + ‖z‖) ^ 3
      ≤ (Real.exp (B ^ 2) * Real.exp (-y ^ 2)) * (16 * T ^ 4 * Real.exp (y ^ 2)) :=
        mul_le_mul hexp (hz3.trans hu4) (by positivity) (by positivity)
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) * (Real.exp (-y ^ 2) * Real.exp (y ^ 2)) := by ring
    _ = 16 * T ^ 4 * Real.exp (B ^ 2) := by
        rw [← Real.exp_add]; simp

theorem dGood : DGood := by
  intro a N ha
  obtain ⟨hd, hg⟩ := ha
  have hE : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * a z :=
    (Complex.differentiable_exp.comp (differentiable_id.pow 2)).mul hd
  have key : ∀ b c : ℝ, ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖) ≤ M := by
    intro b c
    obtain ⟨M₁, hM₁, h₁⟩ := gauss_bound b c
    obtain ⟨M₂, h₂⟩ := hg b c
    refine ⟨|M₂| * M₁, by positivity, fun z hb hc => ?_⟩
    have hz := h₁ z hb hc
    have ha' : ‖a z‖ ≤ |M₂| * (1 + ‖z‖) ^ 2 :=
      (h₂ z hb hc).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    rw [norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖a z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (|M₂| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M₂| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 3) := by ring
      _ ≤ |M₂| * M₁ := by gcongr
  refine ⟨⟨hE, fun b c => ?_⟩, ⟨(differentiable_id.sub_const N).mul hE, fun b c => ?_⟩⟩
  · obtain ⟨M, _, h⟩ := key b c
    refine ⟨M, fun z hb hc => (?_ : _ ≤ _).trans (h z hb hc)⟩
    exact le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])
  · obtain ⟨M, hM, h⟩ := key b c
    refine ⟨(1 + ‖N‖) * M, fun z hb hc => ?_⟩
    have hzN : ‖z - N‖ ≤ (1 + ‖N‖) * (1 + ‖z‖) := by
      have := norm_sub_le z N
      nlinarith [norm_nonneg z, norm_nonneg N, mul_nonneg (norm_nonneg z) (norm_nonneg N)]
    rw [norm_mul]
    calc ‖z - N‖ * ‖Complex.exp (z ^ 2) * a z‖
        ≤ ((1 + ‖N‖) * (1 + ‖z‖)) * ‖Complex.exp (z ^ 2) * a z‖ := by gcongr
      _ = (1 + ‖N‖) * (‖Complex.exp (z ^ 2) * a z‖ * (1 + ‖z‖)) := by ring
      _ ≤ (1 + ‖N‖) * M := by
          have := h z hb hc
          gcongr

end GlobalTheory.CompanionTheory.RgEisDGood
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection

namespace GlobalTheory.CompanionTheory.RgEisSide

variable {G : Type} [Group G] [TopologicalSpace G]
  {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem one_toIdele_lemma (y : IdeleGroup k) :
    (((1 : HeckeCharacter k).toIdele y : Circle) : ℂ) = 1 := by
  first
  | rfl
  | simp [HeckeCharacter.toIdele]

theorem side_one {π : G →* GL ι 𝔸[k]} {Γ K P : Subgroup G} {i : ι} {ω : HeckeCharacter k}
    {d : ι → IdeleGroup k} {c : G → ℂ} {η : G → ℝ} (hs : Side π Γ K P i ω d c η) :
    Side π Γ K P i (1 : HeckeCharacter k) d (1 : G → ℂ) η := by
  refine ⟨hs.two, mul_one 1, hs.cont, hs.piK, hs.piΓ, hs.trans, hs.mem,
    ⟨hs.par.closed, hs.par.iwa, ⟨fun _ _ _ _ => by simp, fun _ _ => by simp, fun _ _ _ => rfl,
      continuous_one.continuousOn⟩⟩, hs.ht, fun p hp => ⟨?_, (hs.val p hp).2⟩⟩
  exact (one_toIdele_lemma _).symm

theorem norm_globalZeta_le (F : 𝔸[k] → ℂ) (x : ℝ) :
    ‖globalZeta F (1 : HeckeCharacter k) x‖ ≤
      ∫ t : IdeleGroup k, ‖F (t : 𝔸[k])‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ∂ideleMeasure k := by
  unfold GroundTheory.Global.globalZeta
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_mul, norm_mul, one_toIdele_lemma, norm_one, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k t).2, Complex.ofReal_re]

private theorem stab_lemma {R : Type} [CommRing R] (h : GL ι R) (i : ι) (a b : R)
    (h1 : (h : Matrix ι ι R).mulVec (Pi.single i 1) = a • Pi.single i 1)
    (h2 : ((h⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) = b • Pi.single i 1) :
    h ∈ stab R {i} := by
  show ∀ r ∉ ({i} : Set ι), ∀ c ∈ ({i} : Set ι),
    (h : Matrix ι ι R) r c = 0 ∧ ((h⁻¹ : GL ι R) : Matrix ι ι R) r c = 0
  intro r hr c hc
  rw [Set.mem_singleton_iff] at hc hr
  subst hc
  constructor
  · have := congrFun h1 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this
  · have := congrFun h2 r
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hr] using this

private theorem stab_lemma_2 {R : Type} [CommRing R] (X Y : GL ι R) (i : ι) (c₁ c₂ : Rˣ)
    (h : (c₁ : R) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      (c₂ : R) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1)) :
    Y * X⁻¹ ∈ stab R {i} := by
  have hX : ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₁⁻¹ : R) * c₂) • ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]
  have hY : ((Y⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) =
      ((↑c₂⁻¹ : R) * c₁) • ((X⁻¹ : GL ι R) : Matrix ι ι R).mulVec (Pi.single i 1) := by
    rw [mul_smul, h, smul_smul, Units.inv_mul, one_smul]
  apply stab_lemma (Y * X⁻¹) i ((↑c₁⁻¹ : R) * c₂) ((↑c₂⁻¹ : R) * c₁)
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hX, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Units.mul_inv, Matrix.one_mulVec]
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, hY, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

private theorem vec_mul_lemma_3 (A B : GL ι 𝔸[k]) (i : ι) :
    vec (A * B) i = ((B⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec A i) := by
  unfold PositivityTheory.RgEis.MG.vec
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

theorem sideConv : EpConv → TestSph → Lines → Term → SideConv := by
  intro hEp hTest hLines hTerm
  unfold PositivityTheory.RgEis.MG.SideConv
  intro G _ _ _ _ K hK k _ _ ι _ _ π Γ P i ω d c η hs x hx
  unfold PositivityTheory.RgEis.Conv
  intro g
  have hs1 := side_one hs
  have hcard : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hs.two
  have hx1 : (1 : ℝ) < x := by linarith
  obtain ⟨Ψ, Ψ₁, hΨ, -, -, hsph, hZ⟩ := hTest k ι i
  obtain ⟨-, hT⟩ := hTerm G K hK k ι π Γ P i 1 d 1 η hs1
  obtain ⟨hline, -, hscale⟩ := hT Ψ (x : ℂ)
  obtain ⟨e, he⟩ := hLines G K hK k ι π Γ P i ω d c η hs
  obtain ⟨-, hconv⟩ := hEp k ι Ψ hΨ
  obtain ⟨u, hu, hub⟩ := hconv x {(π g * dgl d)⁻¹} (max_lt hx1 hx) isCompact_singleton
  have hzt : ∀ κ ∈ K, zt π d i Ψ (1 : HeckeCharacter k) (x : ℂ) κ =
      globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ) := by
    intro κ hκ
    show globalZeta (fun t => Ψ (t • vec (kap π d κ) i)) (1 : HeckeCharacter k) (x : ℂ) = _
    congr 1
    funext t
    exact hsph t ⟨kap π d κ, hs.piK κ hκ⟩
  have hA : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ =
        Real.exp (x * η (rep q * g)) * (‖modPow (d i) (x : ℂ)‖ *
          ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖) := by
    intro q
    obtain ⟨p, hp, κ, hκ, hpk⟩ := hs.par.iwa (rep q * g)
    have hη : η (p * κ) = η p := by
      rw [hs.ht.left p hp κ]
      have h1 : η κ = η 1 := by simpa using hs.ht.right 1 κ hκ
      rw [h1, hs.ht.rat 1 (one_mem Γ) (one_mem P), add_zero]
    rw [hpk, hline p hp κ hκ, hzt κ hκ, hη, norm_mul, norm_mul, norm_mul, norm_mul,
      one_toIdele_lemma, Pi.one_apply, norm_one, one_mul, one_mul, ← Complex.ofReal_mul,
      Complex.norm_exp_ofReal]
  have hApos : 0 < ‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖ := by
    refine mul_pos ?_ (norm_pos_iff.mpr (hZ x hx1))
    unfold GroundTheory.Automorphic.GodementSection.modPow
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (IdeleGroup.ideleModule k (d i)).2]
    exact Real.rpow_pos_of_pos (IdeleGroup.ideleModule k (d i)).2 _
  have hbound : ∀ q : Cos P Γ,
      ‖lineZeta Ψ (1 : HeckeCharacter k) (x : ℂ) (vec (π (rep q * g) * dgl d) i)‖ ≤ u (e q) := by
    intro q
    obtain ⟨a, Ha⟩ := he q
    have hw : vec (π (rep q * g) * dgl d) i =
        (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (vec (π (rep q)) i) := by
      rw [map_mul, mul_assoc, vec_mul_lemma_3]
    rw [← hscale a, hw, ← Matrix.mulVec_smul, ← Ha]
    exact (norm_globalZeta_le (fun t => Ψ (t • (((π g * dgl d)⁻¹ : GL ι 𝔸[k]) :
      Matrix ι ι 𝔸[k]).mulVec (ratV (e q).rep))) x).trans (hub _ rfl (e q))
  have hinj : Function.Injective e := by
    intro q₁ q₂ heq
    obtain ⟨a₁, H₁⟩ := he q₁
    obtain ⟨a₂, H₂⟩ := he q₂
    rw [heq] at H₁
    have key : ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₁ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₁))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) =
        ((Units.map (algebraMap k 𝔸[k]).toMonoidHom a₂ : 𝔸[k]ˣ) : 𝔸[k]) •
        (((π (rep q₂))⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]).mulVec (Pi.single i 1) :=
      H₁.symm.trans H₂
    have hst := stab_lemma_2 (π (rep q₁)) (π (rep q₂)) i _ _ key
    rw [← map_inv, ← map_mul] at hst
    have hP := (hs.mem _).mpr hst
    rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
    exact Quotient.sound (QuotientGroup.rightRel_apply.mpr (Subgroup.mem_subgroupOf.mpr hP))
  refine Summable.of_nonneg_of_le (fun q => (Real.exp_pos _).le) (fun q => ?_)
    ((hu.comp_injective hinj).div_const (‖modPow (d i) (x : ℂ)‖ *
      ‖globalZeta (fun t => Ψ₁ fun _ => t) (1 : HeckeCharacter k) (x : ℂ)‖))
  show Real.exp (x * η (rep q * g)) ≤ u (e q) / _
  rw [le_div_iff₀ hApos, ← hA q]
  exact hbound q

end GlobalTheory.CompanionTheory.RgEisSide
end
end

section

noncomputable section

open MeasureTheory Filter Topology
open PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisUnfold

section SlopeTestRemainingChoices

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem integrable_of_continuous (μ : Measure K) [IsProbabilityMeasure μ] {F : K → (W →L[ℂ] W)}
    (hF : Continuous F) : Integrable F μ :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem exists_avgCLM (μ : Measure K) [IsProbabilityMeasure μ] {ρ : K →* (W →L[ℂ] W)}
    (hρ : Continuous ρ) :
    ∃ A : C(K, ℂ) →L[ℂ] (W →L[ℂ] W), ∀ f : C(K, ℂ), A f = avg μ ρ f := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρ.continuousOn
  have hint : ∀ f : C(K, ℂ), Integrable (fun κ => f κ • ρ κ) μ := fun f =>
    integrable_of_continuous μ (f.continuous.smul hρ)
  let A₀ : C(K, ℂ) →ₗ[ℂ] (W →L[ℂ] W) :=
    { toFun := fun f => avg μ ρ f
      map_add' := fun f g => by
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, add_smul]
        exact integral_add (hint f) (hint g)
      map_smul' := fun a f => by
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply]
        exact integral_smul a _ }
  refine ⟨A₀.mkContinuous C fun f => ?_, fun f => rfl⟩
  have h : ∀ᵐ κ ∂μ, ‖f κ • ρ κ‖ ≤ C * ‖f‖ := Eventually.of_forall fun κ => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (hC κ (Set.mem_univ _)) (f.norm_coe_le_norm κ) (norm_nonneg _)
      ((norm_nonneg _).trans (hC κ (Set.mem_univ _)))
  have := norm_integral_le_of_norm_le_const h
  simpa [avg, A₀] using this

theorem avg_translate (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {ρ : K →* (W →L[ℂ] W)} (hρ : Continuous ρ) {φ : K → ℂ} (hφ : Continuous φ) (κ₁ : K) :
    avg μ ρ (fun κ => φ (κ₁ * κ)) = ρ κ₁⁻¹ * avg μ ρ φ := by
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hc : Continuous fun κ : K => κ₁ * κ := continuous_const.mul continuous_id
  have hI : Integrable (fun κ => φ (κ₁ * κ) • ρ (κ₁ * κ)) μ :=
    integrable_of_continuous μ ((hφ.comp hc).smul (hρ.comp hc))
  have h1 : avg μ ρ φ = ∫ κ, φ (κ₁ * κ) • ρ (κ₁ * κ) ∂μ :=
    (integral_mul_left_eq_self (fun κ => φ κ • ρ κ) κ₁).symm
  have h2 := ContinuousLinearMap.integral_comp_comm
    (ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹)) hI
  rw [h1]
  refine Eq.trans ?_ h2
  unfold avg
  refine integral_congr_ae (Eventually.of_forall fun κ => ?_)
  have h3 : (ρ κ₁⁻¹).comp (ρ (κ₁ * κ)) = ρ κ := by
    change ρ κ₁⁻¹ * ρ (κ₁ * κ) = ρ κ
    rw [← map_mul, inv_mul_cancel_left]
  change φ (κ₁ * κ) • ρ κ = ContinuousLinearMap.compL ℂ W W W (ρ κ₁⁻¹) (φ (κ₁ * κ) • ρ (κ₁ * κ))
  rw [map_smul, ContinuousLinearMap.compL_apply, h3]

end SlopeTestRemainingChoices

theorem unfold : SecLaw → AvgMem → Unfold := by
  intro hSec hAvg G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hμ hpr Γ P c hpar φ Λ T hφ hLaw hΛ hT g u hu
    hb w
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have hsec := (hSec G W K ρ hK hρ Γ P c hpar).1
  have hmem := hAvg G W K ρ hK hρ μ hμ hpr Γ P c hpar φ hφ hLaw w
  have key : ∀ q : Cos P Γ, ∃ (p : G) (κ₁ : K), p ∈ P ∧ rep q * g = p * κ₁ := fun q => by
    obtain ⟨p, hp, k, hk, e⟩ := hpar.iwa (rep q * g)
    exact ⟨p, ⟨k, hk⟩, hp, e⟩
  choose p κ₁ hp hpk using key
  have hterm : ∀ q (κ : K), T (rep q * (g * κ)) =
      (c (p q) * Complex.exp (Λ (p q))) * φ (κ₁ q * κ) := fun q κ => by
    have e : rep q * (g * (κ : G)) = p q * ((κ₁ q * κ : K) : G) := by
      rw [← mul_assoc, hpk q, Subgroup.coe_mul, mul_assoc]
    rw [e]
    exact hT _ (hp q) _
  have hc : ∀ q, Continuous fun κ : K => φ (κ₁ q * κ) := fun q =>
    hφ.comp (continuous_const.mul continuous_id)
  let f' : Cos P Γ → C(K, ℂ) := fun q => ⟨fun κ => φ (κ₁ q * κ), hc q⟩
  let f : Cos P Γ → C(K, ℂ) := fun q => (c (p q) * Complex.exp (Λ (p q))) • f' q
  have hfa : ∀ q κ, f q κ = T (rep q * (g * κ)) := fun q κ => by
    rw [hterm]
    simp [f, f']
  have hu0 : ∀ q, 0 ≤ u q := fun q => (norm_nonneg _).trans (hb q 1)
  have hsum : Summable f := Summable.of_norm_bounded hu fun q =>
    (ContinuousMap.norm_le _ (hu0 q)).2 fun κ => by
      rw [hfa]
      exact hb q κ
  obtain ⟨A, hA⟩ := exists_avgCLM μ hρ
  have hF : (fun κ : K => ∑' q : Cos P Γ, T (rep q * (g * κ))) = ⇑(∑' q, f q) := by
    funext κ
    rw [← ContinuousMap.tsum_apply hsum]
    exact tsum_congr fun q => (hfa q κ).symm
  rw [hF, ← hA]
  have hL := ((ContinuousLinearMap.apply ℂ W w).comp A).map_tsum hsum
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] at hL
  rw [hL]
  unfold eis
  refine tsum_congr fun q => ?_
  have e1 : A (f q) w = (c (p q) * Complex.exp (Λ (p q))) • (ρ (κ₁ q)⁻¹ (avg μ ρ φ w)) := by
    have : A (f' q) = ρ (κ₁ q)⁻¹ * avg μ ρ φ := by
      rw [hA]
      exact avg_translate μ hρ hφ (κ₁ q)
    have e2 : A (f q) = (c (p q) * Complex.exp (Λ (p q))) • A (f' q) := map_smul A _ _
    rw [e2, this]
    rfl
  rw [e1, hpk q, hΛ _ _ (κ₁ q).2, hsec _ hmem _ (hp q), smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.RgEisUnfold
end
end

section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.trace_element_capelli_recursion : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (P : Polynomial ℂ) (v : V), (∀ u : ℂ, Formalism.REAL.qdet E u v = P.eval u • v) → ∀ (N : ℕ) (t : ℕ → ℂ), (∀ k < N, Formalism.REAL.etr E k v = t k • v) → Formalism.REAL.etr E N v = ((-1 : Polynomial ℂ) ^ N * ((Polynomial.X - Polynomial.C (m : ℂ)) ^ (N + 1) * ((P).comp (Polynomial.X + 1) - (P)) - (P) * ∑ k ∈ Finset.range N, Polynomial.C ((-1) ^ k * t k) * (Polynomial.X - Polynomial.C (m : ℂ)) ^ (N - k))).coeff (m + 1) • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | exact GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen | (intros; apply GlobalTheory.CompanionTheory.CapelliEigen.etr_apply_of_eigen <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.is_sep_closure_of_range_eq : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [Algebra F (Om l)] (K : FinExt l),
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) → IsSepClosure F (Om l) := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range | exact GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range | (intros; apply GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range <;> assumption)
end
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms


theorem _root_.GlobalTheory.T.valuation_le_iff_norm_embedding : ∀ {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (φ : F →+* Om l), Continuous φ → ∀ a b : F, a ≤ᵥ b ↔ ‖φ a‖ ≤ ‖φ b‖ := by
  first | exact @GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | exact GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le | (intros; apply GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le <;> assumption)
end
end
