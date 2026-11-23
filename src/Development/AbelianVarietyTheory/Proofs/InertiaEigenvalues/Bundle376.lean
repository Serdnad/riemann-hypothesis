module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.HCDisjointO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle192
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle005
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle356
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle357
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle012
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle308
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011

@[expose] public section

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.Points

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut (F : IntermediateField ℚ_[l] (Om l)) (f : ↥F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : ↥F, g (x : Om l) = f x := by
  refine ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (AlgHom.normal_bijective _ _ _ _), fun x => ?_⟩
  exact f.liftNormal_commutes (Om l) x

theorem exists_restr {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) (hF : F ≤ Ks K s) :
    ∃ τ : ↥F →ₐ[ℚ_[l]] ↥LL.1, ∀ x : ↥F, (τ x : Om l) = g (x : Om l) :=
  ⟨(g.toAlgHom.comp F.val).codRestrict LL.1.toSubalgebra
    (fun x => h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨x, hF x.2⟩), fun _ => rfl⟩

theorem zeta_pow (P : LocPrime l) (m : ℕ) : P.ζQ m ^ l ^ m = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_pow_one (P : LocPrime l) (m : ℕ) : P.ζQ (m + 1) ^ l ^ m = P.ζQ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_prim (P : LocPrime l) (s : ℕ) (hs : 1 ≤ s) : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hnot : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [zeta_pow_one]; exact P.ζQ_one
  rw [← orderOf_eq_prime_pow hnot (zeta_pow P (m + 1))]
  exact IsPrimitiveRoot.orderOf _

theorem zeta_mem (P : LocPrime l) (K : FinExt l) (s : ℕ) : P.ζQ s ∈ Ks K s :=
  (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zeta_pow P s))

theorem unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := le_sup_left

theorem card_emb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥F] (hF : F ≤ Ks K s) :
    Nat.card (↥F →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥F := by
  have hb : Function.Bijective (fun f : ↥F →ₐ[ℚ_[l]] ↥LL.1 => LL.1.val.comp f) := by
    constructor
    · intro f f' hf
      exact AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hf x)
    · intro f
      obtain ⟨g, hg⟩ := exists_aut F f
      obtain ⟨τ, hτ⟩ := exists_restr h g F hF
      exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (hg x)⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card]
  exact AlgHom.card ℚ_[l] ↥F (Om l)

variable {P : LocPrime l} (H : LocHW l P) {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem pt_of_aut (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : GQ l)
    (h0 : ∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1))
    (hζ : g (P.ζQ s) = ζ) (hτ : ∀ x : ↥K.1, g (x : Om l) = τ x) : Pt H h i ζ τ := by
  obtain ⟨τs, hτs⟩ := exists_restr h g (Ks K s) le_rfl
  refine ⟨τs, ⟨fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩, fun x y hxy => Subtype.ext ?_⟩
  · rw [hτs, hxy, h0]
  · rw [hτs, hy, hζ]
  · rw [hτs, hxy, hτ]

theorem aut_of_pt (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    ∃ g : GQ l, (∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1)) ∧
      g (P.ζQ s) = ζ ∧ ∀ x : ↥K.1, g (x : Om l) = τ x := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  obtain ⟨g, hg⟩ := exists_aut (Ks K s) (LL.1.val.comp τs)
  refine ⟨g, fun c => ?_, ?_, fun x => ?_⟩
  · rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    exact hg ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩
  · rw [← h2 ⟨_, zeta_mem P K s⟩ rfl]
    exact hg ⟨_, zeta_mem P K s⟩
  · rw [h3 x ⟨x, h.2.2.1 x.2⟩ rfl]
    exact hg ⟨x, h.2.2.1 x.2⟩

theorem exists_pt (i : Let K) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) : ∃ τ, Pt H h i ζ τ := by
  obtain ⟨g₀, hg₀⟩ := exists_aut (K0 K) (LL.1.val.comp ((H.W K s LL h).emb i))
  have h1 : IsPrimitiveRoot (g₀.symm (ζ : Om l)) (l ^ s) :=
    (hζ.map_of_injective (f := LL.1.val) LL.1.val.toRingHom.injective).map_of_injective g₀.symm.injective
  have hconj : IsConjRoot ↥(K0 K) (g₀.symm (ζ : Om l)) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ h1,
      GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ (zeta_prim P s h.1)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  obtain ⟨τ, hτ⟩ := exists_restr h ((σ.restrictScalars ℚ_[l]).trans g₀) K.1 h.2.2.1
  refine ⟨τ, pt_of_aut H h i ζ τ ((σ.restrictScalars ℚ_[l]).trans g₀) (fun c => ?_) ?_
    (fun x => (hτ x).symm)⟩
  · have : σ (c : Om l) = c := σ.commutes c
    change g₀ (σ (c : Om l)) = _
    rw [this]
    exact hg₀ c
  · change g₀ (σ (P.ζQ s)) = _
    rw [hσ, AlgEquiv.apply_symm_apply]

theorem pt_props (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    IsPrimitiveRoot ζ (l ^ s) ∧
      τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = (H.W K s LL h).emb i ∧
      ∃ ι, Comp H h i ζ τ ι := by
  obtain ⟨g, h0, hζ, hτ⟩ := aut_of_pt H h i ζ τ hp
  refine ⟨?_, ?_, (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp
    (g.symm.toAlgHom.comp LL.1.val), fun c => ?_, ?_, fun c => ?_⟩
  · have h1 := (zeta_prim P s h.1).map_of_injective g.injective
    rw [hζ] at h1
    exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) h1 LL.1.val.toRingHom.injective
  · refine AlgHom.ext fun c => Subtype.ext ?_
    rw [← h0 c]
    exact (hτ _).symm
  · change algebraMap (Om l) P.R.BdR (g.symm (((H.W K s LL h).emb i c : ↥LL.1) : Om l)) = _
    rw [← h0 c, AlgEquiv.symm_apply_apply]
    rfl
  · change algebraMap (Om l) P.R.BdR (g.symm (ζ : Om l)) = _
    rw [← hζ, AlgEquiv.symm_apply_apply]
  · change algebraMap (Om l) P.R.BdR (g.symm ((τ c : ↥LL.1) : Om l)) = _
    rw [← hτ c, AlgEquiv.symm_apply_apply]
    rfl

theorem exists_pt_over (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ∃ (i : Let K) (ζ : ↥LL.1), Pt H h i ζ τ := by
  obtain ⟨g, hg⟩ := exists_aut K.1 (LL.1.val.comp τ)
  obtain ⟨i, hi⟩ := (H.W K s LL h).emb_bij.2 (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨i, ⟨g (P.ζQ s), h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨_, zeta_mem P K s⟩⟩,
    pt_of_aut H h i _ τ g (fun c => ?_) rfl hg⟩
  rw [hi]
  exact hg (algebraMap ↥(K0 K) ↥K.1 c)

theorem points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ τ, Pt (HW l) h i ζ τ) ∧ (∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → IsPrimitiveRoot ζ (l ^ s) ∧ τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i ∧ ∃ ι, Comp (HW l) h i ζ τ ι) ∧ (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ (i : Let K) (ζ : ↥LL.1), Pt (HW l) h i ζ τ) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) := by
  intro D HW l _ K s LL h
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  exact ⟨exists_pt (HW l) h, pt_props (HW l) h, exists_pt_over (HW l) h,
    card_emb h K.1 h.2.2.1, card_emb h (K0 K) (unramifiedSubfield_le_cyclotomicExt K s)⟩

end GlobalTheory.NL.Points
end
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

namespace GlobalTheory.TypePrimeEta

theorem sum_two_mul_Icc (r : ℕ) : ∑ a ∈ Finset.Icc 1 r, 2 * a = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

theorem padicValNat_pow_sub_one_le (g g' a : ℕ) (hg : g.Prime) (hg' : 2 ≤ g') (hgg : g' ≤ g ^ 2)
    (ha : 1 ≤ a) : padicValNat g (g' ^ a - 1) ≤ 2 * a := by
  haveI : Fact g.Prime := ⟨hg⟩
  have h1 : 1 < g' ^ a := Nat.one_lt_pow (by omega) (by omega)
  have hpos : 0 < g' ^ a - 1 := by omega
  have hle : g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := Nat.le_of_dvd hpos (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hlt : g ^ padicValNat g (g' ^ a - 1) < g ^ (2 * a) := by
    calc g ^ padicValNat g (g' ^ a - 1) ≤ g' ^ a - 1 := hle
      _ < g' ^ a := by omega
      _ ≤ (g ^ 2) ^ a := Nat.pow_le_pow_left hgg a
      _ = g ^ (2 * a) := by rw [← pow_mul]
  by_contra h
  have h := Nat.lt_of_not_le h
  have := Nat.pow_le_pow_right hg.pos h.le
  omega

theorem val_card_le (g g' r f : ℕ) (hg : g.Prime) (hg' : g'.Prime) (hne : g ≠ g')
    (hgg : g' ≤ g ^ 2) :
    padicValNat g (Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g)) ^ f *
      Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod g')) ^ f) ≤ 2 * f * r ^ 2 := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : Fact g'.Prime := ⟨hg'⟩
  have h0 : ∀ q : ℕ, [Fact q.Prime] → Nat.card (Matrix.GeneralLinearGroup (Fin r) (ZMod q)) ≠ 0 :=
    fun q _ => Nat.card_pos.ne'
  obtain ⟨h1, h2⟩ := Formalism.IrreducibleCountingLemmas.WindowSums.padicValCardGeneralLinear g g' r hne
  have hpow (a n : ℕ) : padicValNat g (a ^ n) = n * padicValNat g a := by
    simpa only [← Nat.padicValNat_def] using (Nat.multiplicity_pow (p := g) a n)
  rw [(show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (pow_ne_zero _ (h0 g)) (pow_ne_zero _ (h0 g')), hpow, hpow, h1, h2]
  have hs : ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1) ≤ r * (r + 1) := by
    rw [← sum_two_mul_Icc]
    exact Finset.sum_le_sum fun a ha =>
      padicValNat_pow_sub_one_le g g' a hg hg'.two_le hgg (Finset.mem_Icc.1 ha).1
  have hd : r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ _
  have he : r * (r - 1) + r * (r + 1) = 2 * r ^ 2 := by
    cases r with
    | zero => simp
    | succ n => simp only [Nat.add_sub_cancel]; ring
  calc f * (r * (r - 1) / 2) + f * ∑ a ∈ Finset.Icc 1 r, padicValNat g (g' ^ a - 1)
      ≤ f * (r * (r - 1)) + f * (r * (r + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hd) (Nat.mul_le_mul_left _ hs)
    _ = 2 * f * r ^ 2 := by rw [← mul_add, he]; ring

theorem val_cardG0g_le (D : D7) (k k' : Fin 2) (hkk : k ≠ k')
    (hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)) :
    padicValNat (D.host.g k) D.what₂.restRowsFiniteGroupCard ≤ 2 * D.R.f * D.R.r ^ 2 := by
  have hg := D.host.g_prime k
  have hg' := D.host.g_prime k'
  have hgg : D.host.g k' ≤ D.host.g k ^ 2 := by
    have h1 : (0 : ℝ) < D.host.g k' := by exact_mod_cast hg'.pos
    have h0 : (0 : ℝ) < (D.host.g k : ℝ) ^ 2 := pow_pos (by exact_mod_cast hg.pos) 2
    have h2 : Real.log (D.host.g k' : ℝ) ≤ Real.log ((D.host.g k : ℝ) ^ 2) := by
      rw [Real.log_pow]; push_cast; linarith
    have := (Real.log_le_log_iff h1 h0).1 h2
    exact_mod_cast this
  have hk : (k = 0 ∧ k' = 1) ∨ (k = 1 ∧ k' = 0) := by
    fin_cases k <;> fin_cases k' <;> simp_all
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne hgg
  · rw [D.nd.restN_card_levelGroup_eq, Fin.prod_univ_two, mul_comm]
    exact val_card_le _ _ _ _ hg hg' D.host.g_ne.symm hgg

theorem first_le (f r t CT N r' e n : ℕ) (C : ℝ) (hC : 8 * (CT : ℝ) ≤ C) (hN2 : 2 ≤ N)
    (hN : N ≤ n + 1) (hr4 : 4 * r' ≤ N ^ 2) (hn : r + t = n) :
    ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ) ≤
      4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
  have hn1 : (1 : ℝ) ≤ n := by have : 1 ≤ n := by omega
                               exact_mod_cast this
  have hnR : (n : ℝ) = r + t := by rw [← hn]; push_cast; ring
  have a1 : (4 : ℝ) * r' ≤ (N : ℝ) ^ 2 := by exact_mod_cast hr4
  have a2 : (N : ℝ) ≤ 2 * n := by
    have : N ≤ 2 * n := by omega
    exact_mod_cast this
  have a0 : (0 : ℝ) ≤ N := by positivity
  have a3 : (N : ℝ) ^ 2 ≤ (2 * n) ^ 2 := pow_le_pow_left₀ a0 a2 2
  have hNr : 4 * ((N : ℝ) * r') ≤ 4 * (2 * (n : ℝ) ^ 3) := by
    calc 4 * ((N : ℝ) * r') = N * (4 * r') := by ring
      _ ≤ N * N ^ 2 := mul_le_mul_of_nonneg_left a1 a0
      _ = N ^ 3 := by ring
      _ ≤ (2 * n) ^ 3 := pow_le_pow_left₀ a0 a2 3
      _ = 4 * (2 * (n : ℝ) ^ 3) := by ring
  have hs : (N : ℝ) + r' ≤ 3 * (n : ℝ) ^ 2 := by nlinarith
  have he0 : (0 : ℝ) ≤ e := by positivity
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hr0 : (0 : ℝ) ≤ r' := by positivity
  have hm : ((e : ℝ) + t + 1) * (N + r') ≤ ((e : ℝ) + t + n) * (3 * (n : ℝ) ^ 2) :=
    mul_le_mul (by linarith) hs (by positivity) (by positivity)
  have hX : (N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r') ≤ 5 * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [pow_nonneg (show (0:ℝ) ≤ n by linarith) 2]
  have hY : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((n : ℝ) + e + t) := by positivity
  have hCT : (0 : ℝ) ≤ CT := by positivity
  have hCX : (CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r')) ≤
      C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by
    nlinarith [mul_le_mul_of_nonneg_left hX hCT, mul_le_mul_of_nonneg_right hC hY]
  calc ((f * (2 * ((2 * r + t * 2) * (CT * (N * r' + (e + t + 1) * (N + r'))))) : ℕ) : ℝ)
      = 4 * (f : ℝ) * n * ((CT : ℝ) * ((N : ℝ) * r' + ((e : ℝ) + t + 1) * (N + r'))) := by
        push_cast; rw [hnR]; ring
    _ ≤ 4 * (f : ℝ) * n * (C * ((n : ℝ) ^ 2 * ((n : ℝ) + e + t))) :=
        mul_le_mul_of_nonneg_left hCX (by positivity)
    _ = 4 * (f : ℝ) * n * (C * (n : ℝ) ^ 2 * ((n : ℝ) + e + t)) := by ring

end GlobalTheory.TypePrimeEta

namespace GlobalTheory

end GlobalTheory
end

section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerSys
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys

theorem zIdem_idem_central {Γ : Type} [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (h : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.simpleRepCentralIdempotent_isCentralIdempotent τ h

theorem zIdem_mul_eq_zero {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (hne : zIdem τ ≠ zIdem τ') : zIdem τ * zIdem τ' = 0 := GlobalTheory.T.simpleRepCentralIdempotent_mul_eq_zero_of_ne τ τ' h h' hne

theorem repIso_of_zIdem_eq {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ')
    (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq τ τ' h h' he

theorem zIdem_finite_sum (Γ : Type) [Group Γ] [Fintype Γ] :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := GlobalTheory.T.centralIdempotents_simpleFDRep_finite_finsum_eq_one Γ

section Main

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C)

def Zall (g n : ℕ) [Fact g.Prime] : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z}

def Zl (n : ℕ) (f : (ZMod g)[X]) : Set (MonoidAlgebra ℂ (GL (Fin n) (ZMod g))) :=
  {z | ∃ τ : FDRep ℂ (GL (Fin n) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f}

theorem Zl_sub (n : ℕ) (f : (ZMod g)[X]) : Zl O n f ⊆ Zall g n := fun _ ⟨τ, h1, h2, _⟩ => ⟨τ, h1, h2⟩

theorem Zall_finite (n : ℕ) : (Zall g n).Finite := (zIdem_finite_sum (GL (Fin n) (ZMod g))).1

theorem Zl_finite (n : ℕ) (f : (ZMod g)[X]) : (Zl O n f).Finite := (Zall_finite n).subset (Zl_sub O n f)

theorem eSerO_eq_sum (n : ℕ) (f : (ZMod g)[X]) : eSerO O n f = ∑ z ∈ (Zl_finite O n f).toFinset, z := by
  rw [← finsum_mem_eq_finite_toFinset_sum (fun z => z) (Zl_finite O n f)]
  rfl

theorem mul_of_mem {n : ℕ} {z z' : MonoidAlgebra ℂ (GL (Fin n) (ZMod g))} (hz : z ∈ Zall g n)
    (hz' : z' ∈ Zall g n) : z * z' = if z = z' then z' else 0 := by
  obtain ⟨τ, hτ, rfl⟩ := hz
  obtain ⟨τ', hτ', rfl⟩ := hz'
  split_ifs with h
  · rw [← h]; exact (zIdem_idem_central τ hτ).1
  · exact zIdem_mul_eq_zero τ τ' hτ hτ' h

theorem isConstituent_of_repIso_left {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ'.ρ τ.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, hne⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ (e : (τ' : Type) →ₗ[ℂ] (τ : Type)), fun γ => LinearMap.ext fun x => ?_, fun h0 => hne ?_⟩
  · show φ (e (τ'.ρ γ x)) = ρ γ (φ (e x))
    rw [he]
    exact LinearMap.congr_fun (hφ' γ) (e x)
  · refine LinearMap.ext fun x => ?_
    have := LinearMap.congr_fun h0 (e.symm x)
    simpa using this

theorem hasLabelO_of_repIso {n : ℕ} {τ τ' : FDRep ℂ (GL (Fin n) (ZMod g))} {f : (ZMod g)[X]}
    (h : HasLabelO O τ f) (e : RepIso τ'.ρ τ.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hc, hf⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hc e, hf⟩

end Main

end GlobalTheory.SerOSys
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

namespace GlobalTheory.UseLoc.JumpBlock

theorem reflS_blockJ_iff (D : D7) (q : ℚ) :
    AdmissibleParameterJ.refl D q ∈ AdmissibleParameterJ.blockJ D ↔ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  simp only [AdmissibleParameterJ.refl, AdmissibleParameterJ.blockJ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith
  · rintro ⟨c, hc, hq⟩
    refine ⟨D.R.t - 1 - c, by omega, ?_⟩
    have h1 : 1 ≤ D.R.t := by omega
    rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
    push_cast
    linarith

theorem jumps_iff : ∀ (D : D7) (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) (q : ℚ),
    q ∈ AdmissibleParameterJ.JJ D up j ρ ↔ q ∈ AdmissibleParameterJ.JW D up j ρ ∨ ∃ c : ℕ, c < D.R.t ∧ q = c := by
  intro D up j ρ q
  cases up
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jm, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.reflS,
      Set.mem_union, Set.mem_setOf_eq, Bool.false_eq_true, if_false]
    rw [reflS_blockJ_iff]
  · simp only [AdmissibleParameterJ.JJ, AdmissibleParameterJ.JW, AdmissibleParameterJ.Jp, AdmissibleParameterJ.cloudT, AdmissibleParameterJ.lowT, AdmissibleParameterJ.blockJ,
      Set.mem_union, Set.mem_setOf_eq, if_true]

end GlobalTheory.UseLoc.JumpBlock
end

section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary

namespace GlobalTheory.BridgeAdmDict

theorem sz_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.sz D (D.nd.j i) ρ = (D.hc ρ).e (GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.liftIdx D i) := by
  have := D.nd.j_range i
  unfold AdmissibleParameterJ.sz
  rw [dite_eq_left (by omega)]
  rfl

theorem PPm_eq (D : D7) (i : D.nd.Loc) (ρ : D.what₂.Tau) :
    AdmissibleParameterJ.PPm D (D.nd.j i) ρ = GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP D i ρ := by
  unfold AdmissibleParameterJ.PPm GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.PP GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run
  rw [sz_eq, Finset.range_val]

theorem mem_placesOver (D : D7) (i : D.nd.Loc) (τ₀ : D.host.E →+* Qbar (D.nd.l i))
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : InducesW D.nd i τ₀ w) :
    w ∈ placesOver D.host.E (D.nd.l i) := by
  have h1 := (h ((D.nd.l i : ℕ) : 𝓞 D.host.E)).1
  show ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  apply h1
  have e : τ₀ (((D.nd.l i : ℕ) : 𝓞 D.host.E) : D.host.E) = algebraMap ℚ_[D.nd.l i] (PadicAlgCl (D.nd.l i)) (D.nd.l i : ℚ_[D.nd.l i]) := by
    simp
  rw [e, PadicAlgCl.norm_extends]
  simpa using (Padic.norm_p_lt_one (p := D.nd.l i))

end GlobalTheory.BridgeAdmDict
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.finite_image_of_trivial_on_inf_isOpen : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (Q : Type) [Group Q] (ρ : ↥(GK K) →* Q) (J H : Subgroup ↥(GK K)), IsOpen (H : Set ↥(GK K)) → (∀ g ∈ J, g ∈ H → ρ g = 1) → (ρ '' (J : Set ↥(GK K))).Finite := by
  first | exact @GlobalTheory.GK.finite_image_of_trivial_on_open | exact GlobalTheory.GK.finite_image_of_trivial_on_open | (intros; apply GlobalTheory.GK.finite_image_of_trivial_on_open <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := by
  first | exact @GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | exact GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic | (intros; apply GlobalTheory.CycDegRam.tr_lt_finrank_cyclotomic <;> assumption)
end
