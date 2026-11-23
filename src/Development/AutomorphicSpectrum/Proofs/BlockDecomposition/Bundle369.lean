module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle084
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle168
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle110
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle112
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle350
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle329
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle317
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle354
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRowM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle356
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle335
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn

@[expose] public section

section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD

theorem fibres (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (hρ : ρ ≠ 0) (a : FQ F) (b : FQ F) :
    Finite {D : FQ F // a + ρ • D = b} ∧
      Nat.card {D : FQ F // a + ρ • D = b} ≤ Ideal.absNorm (Ideal.span {ρ}) := by
  have hne : Ideal.span {ρ} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hρ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.torsion_card_le_absNorm_pow F 1 (intVec F 1) (isLat_intVec 1) (Ideal.span {ρ}) hne
  rw [pow_one] at hcard
  by_cases hb : ∃ D₀ : FQ F, a + ρ • D₀ = b
  · obtain ⟨D₀, hD₀⟩ := hb
    let φ : {D : FQ F // a + ρ • D = b} → {x : FQ F // ∀ r ∈ Ideal.span {ρ}, r • x = 0} :=
      fun D => ⟨D.1 - D₀, by
        intro r hr
        obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        have h1 : ρ • (D.1 - D₀) = 0 := by
          have h2 : a + ρ • D.1 = a + ρ • D₀ := D.2.trans hD₀.symm
          rw [smul_sub, sub_eq_zero]
          exact add_left_cancel h2
        rw [mul_smul, h1, smul_zero]⟩
    have hφ : Function.Injective φ := by
      intro x y hxy
      have h3 : x.1 - D₀ = y.1 - D₀ := congrArg Subtype.val hxy
      exact Subtype.ext (sub_left_inj.1 h3)
    have hF : Finite {D : FQ F // a + ρ • D = b} := Finite.of_injective φ hφ
    exact ⟨hF, (Nat.card_le_card_of_injective φ hφ).trans hcard⟩
  · have hE : IsEmpty {D : FQ F // a + ρ • D = b} := ⟨fun D => hb ⟨D.1, D.2⟩⟩
    exact ⟨inferInstance, by simp⟩

theorem den_eq (F : Type) [Field F] [NumberField F] (ρ : 𝓞 F) (f : F) (D : FQ F) :
    den F (f + ((ρ : 𝓞 F) : F) * (Quotient.out D : Fin 1 → F) 0) =
      Ideal.torsionOf (𝓞 F) (FQ F)
        ((Submodule.Quotient.mk (fun _ => f) : FQ F) + ρ • D) := by
  unfold den
  congr 1
  have hD : D = Submodule.Quotient.mk (Quotient.out D : Fin 1 → F) :=
    (Quotient.out_eq D).symm
  conv_rhs => rw [hD]
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  funext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp [Algebra.smul_def]

theorem term_le (A δ N n : ℕ) (s : ℝ) (hs : 0 < s) (hδ : δ ≠ 0) (hN : N ≠ 0) (hn : n ≠ 0)
    (h : δ * N ^ 2 * n ^ 2 ≤ A) :
    (A : ℝ) ^ (-s) ≤ (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hle : (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ A := by exact_mod_cast h
  have hpos : (0 : ℝ) < (δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  have hsq : ∀ x : ℝ, 0 < x → (x ^ 2) ^ (-s) = x ^ (-(2 * s)) := by
    intro x hx
    rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  calc (A : ℝ) ^ (-s) ≤ ((δ : ℝ) * (N : ℝ) ^ 2 * (n : ℝ) ^ 2) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
    _ = (δ : ℝ) ^ (-s) * (N : ℝ) ^ (-(2 * s)) * (n : ℝ) ^ (-(2 * s)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), hsq _ hN', hsq _ hn']

theorem sum_delta_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : Matrix (Fin m) (Fin m) E), (∀ a b, σ (c b a) = c a b) → ∀ (u : Fin m → E) (s : ℝ), 1 < s → Summable (fun D : FQ F => (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)) ∧ ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤ C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨C, hC, hmink⟩ := GlobalTheory.T.ideal_principal_element_norm_bound E
  refine ⟨C, hC, ?_⟩
  intro m c hc u s hs
  have hT : tor c u ≠ ⊥ :=
    GlobalTheory.T.lattice_quotient_torsion_nonzero E m (lam c) (GlobalTheory.T.lam_is_lattice E m c) (Submodule.Quotient.mk u)
  obtain ⟨t, htT, ht0, htC⟩ := hmink (tor c u) hT
  obtain ⟨f, hf⟩ := GlobalTheory.T.delta_block_lower_bound_torsion F E σ hσ m c hc u t htT ht0
  have hkt : Ideal.absNorm (Ideal.span {RingOfIntegers.norm F t}) =
      Ideal.absNorm (Ideal.span {t}) := (GlobalTheory.T.relative_norm_cm_absNorm F E σ hσ t).2
  have hNt : Ideal.absNorm (Ideal.span {t}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa [Ideal.span_singleton_eq_bot] using ht0
  have hρ : RingOfIntegers.norm F t ≠ 0 := by
    intro h0
    rw [h0] at hkt
    apply hNt
    rw [← hkt]
    simp
  generalize hρdef : RingOfIntegers.norm F t = ρ at hf hkt hρ
  have hδ : delta c ≠ 0 := (GlobalTheory.T.delta_eq_lattice_index E m c).1
  have hN : Ideal.absNorm (tor c u) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hT
  have hδ' : (0 : ℝ) < delta c := by exact_mod_cast Nat.pos_of_ne_zero hδ
  have hN' : (0 : ℝ) < Ideal.absNorm (tor c u) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hs0 : 0 < s := by linarith
  obtain ⟨hsum, hzeta⟩ := GlobalTheory.T.torsion_norm_zeta_bound F 1 (intVec F 1) (isLat_intVec 1) (2 * s - 1) (by linarith)
  have hexp : (((1 : ℕ) : ℝ) + (2 * s - 1)) = 2 * s := by
    push_cast
    ring
  rw [hexp] at hsum hzeta
  let g : FQ F → ℝ := fun x => (Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) x) : ℝ) ^ (-(2 * s))
  have hg0 : ∀ x, 0 ≤ g x := fun x => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let a : FQ F := Submodule.Quotient.mk (fun _ => f)
  let π : FQ F → FQ F := fun D => a + ρ • D
  obtain ⟨hsum2, hle2⟩ := GlobalTheory.T.tsum_comp_bounded_fibres_le (FQ F) (FQ F) π (Ideal.absNorm (Ideal.span {ρ}))
    (fun b => fibres F ρ hρ a b) g hg0 hsum
  let P : ℝ := (delta c : ℝ) ^ (-s) * (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s))
  have hP : 0 ≤ P := by positivity
  have hterm : ∀ D : FQ F,
      (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) ≤
        P * g (π D) := by
    intro D
    have h1 := hf ((Quotient.out D : Fin 1 → F) 0)
    rw [den_eq F ρ f D] at h1
    have hn : Ideal.absNorm (Ideal.torsionOf (𝓞 F) (FQ F) (π D)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact GlobalTheory.T.lattice_quotient_torsion_nonzero F 1 (intVec F 1) (isLat_intVec 1) (π D)
    exact term_le _ _ _ _ s hs0 hδ hN hn h1
  have hnn : ∀ D : FQ F,
      0 ≤ (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s) :=
    fun D => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsumP : Summable (fun D : FQ F => P * g (π D)) := hsum2.mul_left P
  refine ⟨Summable.of_nonneg_of_le hnn hterm hsumP, ?_⟩
  have hS : 0 ≤ ∑' x, g x := tsum_nonneg hg0
  have hZ : 0 ≤ zetaR F (2 * s - 1) := hS.trans hzeta
  have hkC : (Ideal.absNorm (Ideal.span {ρ}) : ℝ) ≤ C * Ideal.absNorm (tor c u) := by
    rw [hkt]
    exact htC
  have hpow : (Ideal.absNorm (tor c u) : ℝ) ^ (-(2 * s)) * (Ideal.absNorm (tor c u) : ℝ) =
      (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
    rw [show (1 - 2 * s) = -(2 * s) + 1 by ring, Real.rpow_add hN', Real.rpow_one]
  calc ∑' D : FQ F, (delta (blk σ c u (algebraMap F E ((Quotient.out D : Fin 1 → F) 0))) : ℝ) ^ (-s)
      ≤ ∑' D : FQ F, P * g (π D) :=
        (Summable.of_nonneg_of_le hnn hterm hsumP).tsum_le_tsum hterm hsumP
    _ = P * ∑' D : FQ F, g (π D) := tsum_mul_left
    _ ≤ P * ((Ideal.absNorm (Ideal.span {ρ}) : ℝ) * ∑' x, g x) :=
        mul_le_mul_of_nonneg_left hle2 hP
    _ ≤ P * ((C * Ideal.absNorm (tor c u)) * zetaR F (2 * s - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        exact mul_le_mul hkC hzeta hS (by positivity)
    _ = C * zetaR F (2 * s - 1) * (delta c : ℝ) ^ (-s) *
          (Ideal.absNorm (tor c u) : ℝ) ^ (1 - 2 * s) := by
        rw [← hpow]
        simp only [P]
        ring

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumD
end
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open GlobalTheory.CompanionTheory.FineProd (dropHom)

namespace GlobalTheory.CompanionTheory.WordProd.RowCell

section Blocks

variable {r r' N : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
  (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o)

def dropSigma : (Σ a, Fin (d (o a))) ≃ (Σ j, Fin (d j)) :=
  Equiv.ofBijective (fun p => ⟨o p.1, p.2⟩) (by
    constructor
    · rintro ⟨a, t⟩ ⟨b, s⟩ h
      obtain rfl : a = b := ho.injective (congrArg Sigma.fst h)
      simpa using h
    · rintro ⟨j, t⟩
      obtain ⟨a, rfl⟩ := hz j (Nat.pos_iff_ne_zero.1 (Fin.pos t))
      exact ⟨⟨a, t⟩, rfl⟩)

def dropPlacing (f : (Σ j, Fin (d j)) ≃ Fin N) : (Σ a, Fin (d (o a))) ≃ Fin N :=
  (dropSigma d o ho hz).trans f

@[simp] theorem dropPlacing_apply (f : (Σ j, Fin (d j)) ≃ Fin N) (a : Fin r') (t : Fin (d (o a))) :
    dropPlacing d o ho hz f ⟨a, t⟩ = f ⟨o a, t⟩ := rfl

variable (k : Type) [Field k] (f : (Σ j, Fin (d j)) ≃ Fin N)

theorem mem_parab_dropPlacing (g : GL (Fin N) k) :
    g ∈ parab k f ↔ g ∈ parab k (dropPlacing d o ho hz f) := by
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    exact h a b i j (ho.lt_iff_lt.1 hab)

theorem mem_unipRad_dropPlacing (g : GL (Fin N) k) :
    g ∈ unipRad k f ↔ g ∈ unipRad k (dropPlacing d o ho hz f) := by
  rw [mem_unipRad, mem_unipRad, ← mem_parab_dropPlacing d o ho hz k f g]
  refine and_congr_right fun _ => ⟨fun h a i j => h (o a) i j, fun h a i j => ?_⟩
  obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
  exact h a i j

theorem leviEmb_dropPlacing (g : Levi k fun j => Fin (d j)) :
    leviEmb k f g = leviEmb k (dropPlacing d o ho hz f) (dropHom d o g) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, dropPlacing_apply, dropPlacing_apply, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne k _ _ hab, dropPlacing_apply, dropPlacing_apply,
      leviEmb_apply_ne k _ _ (ho.injective.ne hab)]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSubquotient_pullback {G L W : Type} [Group G] [Group L] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (s : L →* G) (h : IsSubquotient σ ρ) :
    IsSubquotient (σ.comp s) (ρ.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩, hf⟩

theorem jac_dropPlacing_equiv (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (f : (Σ j, Fin (d j)) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((_root_.GlobalTheory.SmGL.jac f π).Equiv
      ((_root_.GlobalTheory.SmGL.jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _)) := by
  have hs' : ∀ g, ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) g ∈
      Subgroup.normalizer (unipRad k (dropPlacing d o ho hz f) : Set (GL (Fin N) k)) :=
    fun g => leviEmb_mem_normalizer k _ _
  obtain ⟨φ⟩ := Placing.jacquet_equiv π (N := unipRad k f) (N' := unipRad k (dropPlacing d o ho hz f))
    (s := leviEmb k f) (s' := (leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o))
    (leviEmb_mem_normalizer k f) hs' (deltaHalf k fun j => Fin (d j))⁻¹ 1
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).1 hu)
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).2 hu)
    (fun g => by simpa using leviEmb_dropPlacing d o ho hz k f g)
  have e : _root_.GlobalTheory.SmGL.twist (jacquet π (unipRad k (dropPlacing d o ho hz f))
      ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) hs')
        (deltaHalf k fun j => Fin (d j))⁻¹ =
      ((_root_.GlobalTheory.SmGL.jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [_root_.GlobalTheory.SmGL.twist_apply, MonoidHom.comp_apply]
    show _ = _root_.GlobalTheory.SmGL.twist _ _ _ v
    rw [_root_.GlobalTheory.SmGL.twist_apply, MonoidHom.inv_apply, MonoidHom.inv_apply,
      GlobalTheory.CompanionTheory.FineProd.ProdDrop.deltaHalf_drop d o ho hz g]
    rfl
  rw [← e]
  exact ⟨φ⟩

theorem jhMult_jac_ne_zero_of_jm (y : Fin r → IrrGL (k := k)) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) (hd : ∑ a, (y (o a)).1 = N)
    (f : (Σ j, Fin (y j).1) ≃ Fin N) (π : Representation ℂ (GL (Fin N) k) V)
    (h : jm (fun a => y (o a)) hd π ≠ 0) :
    jhMult (piTensor fun j => (y j).rep) (_root_.GlobalTheory.SmGL.jac f π) ≠ 0 := by
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨ψ⟩ := jac_dropPlacing_equiv (fun j => (y j).1) o ho hz f π
  obtain ⟨χ⟩ := (Placing.parInd_jac_placing k _ _ _
    (stdBlocks (fun a => (y (o a)).1) hd) (dropPlacing (fun j => (y j).1) o ho hz f) V).2 π
  have h1 : IsSubquotient (piTensor fun a => (y (o a)).rep)
      (_root_.GlobalTheory.SmGL.jac (dropPlacing (fun j => (y j).1) o ho hz f) π) :=
    (jhMult_ne_zero_iff.1 h).trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)
  have h2 := isSubquotient_pullback (dropHom (k := k) (fun j => (y j).1) o) h1
  exact jhMult_ne_zero_iff.2
    ((IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
      (h2.trans (.of_injective ψ.symm.toIntertwiningMap ψ.symm.toLinearEquiv.injective)))

end Local

theorem sigma_clOf {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL (k := k)) (d : ℕ) (h : d = x.1) : (⟨d, clOf x d⟩ : IrrGL (k := k)) = x := by
  subst h
  exact Sigma.ext rfl (heq_of_eq (clOf_self x))

theorem jhMult_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL (k := k)) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (_root_.GlobalTheory.SmGL.jac f π) ≠ 0 := by
  intro k _ _ _ _ n p N V _ _ π _ zz σ c hc h0 hz f h
  let y : Fin n → IrrGL (k := k) := fun j => ⟨c j, clOf (zz j) (c j)⟩
  have hy : (fun a => y (σ a)) = fun a => zz (σ a) := funext fun a => sigma_clOf _ _ (hc a)
  have key : ∀ (x x' : Fin p → IrrGL (k := k)) (_ : x = x') (hx : ∑ a, (x a).1 = N) (hx' : ∑ a, (x' a).1 = N),
      jm x hx π = jm x' hx' π := by
    rintro x _ rfl _ _
    rfl
  have hd : ∑ a, (y (σ a)).1 = N := by
    rw [← hz]
    exact Finset.sum_congr rfl fun a _ => hc a
  exact jhMult_jac_ne_zero_of_jm y σ σ.strictMono
    (fun j hj => by_contra fun hn => hj (h0 j hn)) hd f π (by rwa [key _ _ hy hd hz])

end GlobalTheory.CompanionTheory.WordProd.RowCell

end
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.haar_measure_open_nonempty_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (E C : Set (Fin t → k)) (hE : IsOpen E) (hn : E.Nonempty) (hC : IsCompact C) (hEC : E ⊆ C),
    ((muD k t) E).toReal ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.muD_toReal_ne_zero <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.integral_mulVec_change_modulus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (w : GL (Fin n) k) (F : (Fin n → k) → W),
  IsLocallyConstant F → HasCompactSupport F →
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun d => F ((w⁻¹ : GL (Fin n) k).1.mulVec d)) =
    ((dpow n 1 w : ℂˣ) : ℂ) • @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | exact GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Scale.smInt_subst <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_commute_shifted_embedding : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : MirabolicParabolic k (i + 1) t) (d : Fin (t + 1) → k), ∃ u : HPG k (i + 1) (t + 1), (pgProj k (i + 1) (t + 1) u).1 ∈ MirUin k (i + 1) ∧ (pgProj k (i + 1) (t + 1) u).2 = 1 ∧ dEmb k i t d * sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) = sEmb k ((i + 1) + t) (h : Mir k ((i + 1) + t)) * (u : Mir k ((i + 1) + t + 1)) * dEmb k i t (((((gpProj k (i + 1) t h).2 : Mir k t) : GL (Fin (t + 1)) k)⁻¹ : GL (Fin (t + 1)) k).val *ᵥ d) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb | exact GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.DConj.dEmb_mul_sEmb <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_cell_double_coset_uniqueness : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (r : Mir k ((i + 1) + t)) (d d' : Fin (t + 1) → k), ∀ h ∈ HPG k (i + 1) (t + 1),
  dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) r = h * dEmb k i t d' * wEl k i t →
  ∃ h' ∈ HPG k i (t + 1), castM k (by omega) h' = r := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | exact GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Stab.mem_of_double_coset <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.weyl_conj_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | exact GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.smooth_vector_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.open_cell_parabolic_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (O : Set (Mir k ((i + 1) + t + 1))) (hO : O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1))),
    ∃ N ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ (h : Mir k ((i + 1) + (t + 1))), h ∈ HPG k (i + 1) (t + 1) →
      ∀ (d : Fin (t + 1) → k) (x : Mir k ((i + 1) + t + 1)), x ∈ N →
        dEmb k i t d * wEl k i t = h * wEl k i t * x → h ∈ O := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.h_small <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_continuous_local_section_of_not_mem_Cl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (p₀ : Mir k ((i + 1) + t + 1)), p₀ ∉ Cl k i t →
  ∃ V ∈ nhds p₀, ∃ μ : Mir k ((i + 1) + t + 1) → Mir k ((i + 1) + t), ContinuousOn μ V ∧
    ∀ p ∈ V, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ d : Fin (t + 1) → k,
      p = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (μ p) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart | exact GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Chart.chart <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unipotent_factorization_character_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (i t : ℕ) (h : HPG k i (t + 1)) (d : Fin (t + 1) → k),
  ∃ (c : HPG k (i + 1) (t + 1)) (u : MirUin k (i + 1)),
    pgProj k (i + 1) (t + 1) c = ((u : Mir k (i + 1)), 1) ∧ mirChar k ψ i u = 1 ∧
    dEmb k i t d * (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) =
      (wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹) * (c : Mir k ((i + 1) + (t + 1))) *
        dEmb k i t ((((pgProj k i (t + 1) h).2)⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj | exact GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Conj.dEmb_conj <;> assumption)
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct


theorem _root_.GlobalTheory.T.haar_measure_coset_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.volume_cosetSet_ne_zero <;> assumption)
end
