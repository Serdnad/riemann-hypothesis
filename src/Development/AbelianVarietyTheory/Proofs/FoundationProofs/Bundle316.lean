module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle010
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle006
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussPowFourHom
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle305
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle309
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)

section Generic

variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}

theorem hecke_induction {p : (G → ℂ) → Prop} (h0 : p 0)
    (hadd : ∀ f ∈ Hecke ℂ K, ∀ f' ∈ Hecke ℂ K, p f → p f' → p (f + f'))
    (hind : ∀ (r : ℂ) (g : G), p (r • dosetInd ℂ K g)) {f : G → ℂ} (hf : f ∈ Hecke ℂ K) : p f := by
  classical
  obtain ⟨e, he⟩ := Final.HeckeBasis G K ℂ
  suffices ∀ a, p (e.symm a) by simpa using this (e ⟨f, hf⟩)
  intro a
  induction a using Finsupp.induction_linear with
  | zero => simpa using h0
  | add a b ha hb => rw [map_add (f := _)]; exact hadd _ (e.symm a).2 _ (e.symm b).2 ha hb
  | single c r =>
    obtain ⟨g, rfl⟩ : ∃ g, DoubleCoset.mk K K g = c := Quotient.exists_rep c
    convert hind r g
    funext x
    rw [← he, e.apply_symm_apply, Finsupp.single_apply, Pi.smul_apply, dosetInd, Set.indicator_apply]
    have : DoubleCoset.mk K K g = DoubleCoset.mk K K x ↔ x ∈ DoubleCoset.doubleCoset g (K : Set G) K := by
      rw [DoubleCoset.eq, DoubleCoset.mem_doubleCoset]; rfl
    by_cases hx : x ∈ DoubleCoset.doubleCoset g (K : Set G) K
    · simp [hx, this.2 hx]
    · simp [hx, mt this.1 hx]

theorem heckeVec_add (hK : IsCommensurated K) (ρ : Representation ℂ G V) {f f' : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (hf' : f' ∈ Hecke ℂ K) (x : V) : heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  simp only [heckeVec, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)

theorem heckeVec_smul (hK : IsCommensurated K) (ρ : Representation ℂ G V) (r : ℂ) {f : G → ℂ} (hf : f ∈ Hecke ℂ K)
    (x : V) : heckeVec ρ K (r • f) x = r • heckeVec ρ K f x := by
  simp only [heckeVec, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (smul_finsum' r (finite_heckeVec hK hf ρ x)).symm

theorem dosetInd_comp (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') (t : H) :
    dosetInd ℂ K' t ∘ e = dosetInd ℂ K (e.symm t) := by
  funext g
  have : e g ∈ DoubleCoset.doubleCoset t (K' : Set H) K' ↔ g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨a, ha, b, hb, h⟩
      exact ⟨e.symm a, (hK _).2 (by simpa using ha), e.symm b, (hK _).2 (by simpa using hb), e.injective (by simpa using h)⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨e a, (hK _).1 ha, e b, (hK _).1 hb, by simp⟩
  by_cases hg : g ∈ DoubleCoset.doubleCoset (e.symm t) (K : Set G) K
  · simp [dosetInd, hg, this.2 hg]
  · simp [dosetInd, hg, mt this.1 hg]

theorem dosetInd_mul {a b : G} (ha : a ∈ K) (hb : b ∈ K) (t : G) : dosetInd ℂ K (a * t * b) = dosetInd ℂ K t := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb, rfl⟩)]

end Generic

section Unitary

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  {σ : w.adicCompletion E →+* w.adicCompletion E} {n q : ℕ} {ϖ : w.adicCompletion E}
  {V : Type} [AddCommGroup V] [Module ℂ V]


open GlobalTheory.InertThetaCompare in
theorem cartanU (hU : IsUnramInv ϖ σ q) (g : GU σ n) : ∃ (d : Fin n → ℤ) (t : GU σ n), Antitone d ∧
    t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  have hϖ : IsUnifV E w ϖ := hU.2.2.2.1
  obtain ⟨d, hd, k₁, h₁, k₂, h₂, e⟩ := Final.CartanDecomp E w n ϖ (mem_Ov_of_isUnifV hϖ) hϖ g.1
  obtain ⟨h, hh, eh⟩ := exists_antiJ_frame hU n
  have hh' : h ∈ GLint (Fin n) (Ov E w) := hh
  have hd' : ∀ i : Fin n, (List.ofFn d).getD i.1 0 = d i := fun i => by simp [List.getD_eq_getElem?_getD]
  have hG : Good n (List.ofFn d) := good_of_unitary hU (π := ϖ) hϖ (by simp)
    (List.pairwise_ofFn.2 fun i j hij => hd hij.le)
    (GlobalTheory.InertDoubleCoset.conj_mem_UJ σ (GlobalTheory.InertDoubleCoset.inv_frame σ eh) g.2)
    ⟨h * k₁, mul_mem hh' h₁, k₂ * h⁻¹, mul_mem h₂ (inv_mem hh'), by
      simp only [Units.val_mul, e, hd', inv_inv, Matrix.mul_assoc]; rfl⟩
  obtain ⟨t, ht, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => ϖ ^ (List.ofFn d).getD i.1 0) fun i => by
    rw [map_zpow₀, hU.2.2.1, hG.rev, ← zpow_add₀ (unif_ne_zero hU), add_neg_cancel, zpow_zero]
  simp only [hd'] at ht
  exact ⟨d, t, hd, ht, dc_GU hU (a := k₁) (b := k₂) h₁ h₂ (Units.ext (by simp only [Units.val_mul, ht]; exact e))⟩

theorem isSatVecU_of_diag (hU : IsUnramInv ϖ σ q) {ρ : Representation ℂ (GU σ n) V} {x : V} {α : Fin (n / 2) → ℂˣ}
    (h0 : x ≠ 0) (hx : x ∈ fixed ρ (KU σ n))
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      heckeVec ρ (KU σ n) (dosetInd ℂ (KU σ n) t) x = SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) • x) :
    IsSatVecU ϖ q ρ x α := by
  obtain ⟨y, hy⟩ := (hasSatU_psFunU hU α).exists_vec
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hm := Final.DosetIndMem _ (KU σ n) ℂ
  refine ⟨h0, hx, fun f hf => ?_⟩
  refine hecke_induction (K := KU σ n)
    (p := fun f => heckeVec ρ (KU σ n) f x = SatU ϖ q f (fun i => (α i : ℂ)) • x) ?_ ?_ ?_ hf
  · simp [heckeVec, SatU]
  · intro f hf f' hf' h1 h2
    have := hy.2.2 _ (add_mem hf hf')
    rw [heckeVec_add hK _ hf hf', hy.2.2 _ hf, hy.2.2 _ hf', ← add_smul] at this
    rw [heckeVec_add hK _ hf hf', h1, h2, ← add_smul, smul_left_injective ℂ hy.1 this]
  · intro r g
    obtain ⟨d, t, hd, ht, k₁, h₁, k₂, h₂, rfl⟩ := cartanU hU g
    rw [dosetInd_mul h₁ h₂]
    have := hy.2.2 _ (Submodule.smul_mem _ r (hm t))
    rw [heckeVec_smul hK _ r (hm t), hy.2.2 _ (hm t), smul_smul] at this
    rw [heckeVec_smul hK _ r (hm t), h d t hd ht, smul_smul, smul_left_injective ℂ hy.1 this]

end Unitary

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E))
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]

def IsEigenSys (h : w.under (𝓞 F) = v) (ρ : Representation ℂ (GLoc σ J v) V) (x : V) (c : List ℤ → ℂ) : Prop :=
  ∀ (a : GL (Fin n) (w.adicCompletion E)) (g : GLoc σ J v) (d : Fin n → ℤ) (u : Fin n → w.adicCompletion E),
    IsFrameAt w L a → Antitone d → (∀ i, Valued.v (u i) = WithZero.exp (-d i)) →
    (a⁻¹ * locMat σ J h g * a).1 = Matrix.diagonal u →
    heckeVec ρ (stabLoc σ J L v) (dosetInd ℂ (stabLoc σ J L v) g) x = c (List.ofFn d) • x

variable {σ J L} {h : w.under (𝓞 F) = v} {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {c : List ℤ → ℂ}
  {B : Multiset ℂˣ}

theorem IsEigenSys.split (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {e : GLoc σ J v ≃* GL (Fin n) (w.adicCompletion E)} (he : IsSplitChart σ J L h e) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x =
      c (List.replicate j 1 ++ List.replicate (n - j) 0) • x := by
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  let t : GL (Fin n) (w.adicCompletion E) := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (by
    rw [diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0])
  have ht : Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (KGL w (n := n)) t := by
    rw [Tj, dosetInd]
    congr 1
    ext g
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, Units.ext e⟩,
      fun ⟨a, ha, b, hb, e⟩ => ⟨a, ha, b, hb, congrArg Units.val e⟩⟩
  obtain ⟨⟨a, ha, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Tj_mem_hecke hϖ j).1 hx, ht, dosetInd_comp e e2,
    hc a (e.symm t) (fun i => if i.1 < j then 1 else 0) (fun i => if i.1 < j then ϖ else 1) ha
      (fun i k hik => ?_) (fun i => ?_) (by rw [← e1, e.apply_symm_apply]; rfl)]
  · congr 2
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    by_cases hi : i < j <;> simp [hi, List.getElem_append]
  · have : i.1 ≤ k.1 := hik
    dsimp only
    split_ifs <;> omega
  · split_ifs
    · exact hϖ
    · simp

theorem IsEigenSys.inert (hc : IsEigenSys σ J L h ρ x c) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    {τ : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU τ n} (he : IsInertChart σ J L h τ e)
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {d : Fin n → ℤ} {t : GU τ n} (hd : Antitone d)
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    heckeVec (ρ.comp e.symm.toMonoidHom) (KU τ n) (dosetInd ℂ (KU τ n) t) x = c (List.ofFn d) • x := by
  obtain ⟨-, ⟨a, ha, -, e1⟩, e2⟩ := he
  rw [heckeVec_comp_symm e e2 (Final.DosetIndMem _ _ ℂ t).1 hx, dosetInd_comp e e2,
    hc a (e.symm t) d _ ha hd (fun i => ?_) (by rw [← e1, e.apply_symm_apply, ht])]
  rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
  simp

theorem IsEigenSys.isSysParam (hc : IsEigenSys σ J L h ρ x c) (hB : IsParamVec σ J L h ρ x B) :
    IsSysParam σ n h c B := by
  have hx := hB.mem_fixed
  rcases hB with ⟨hv, e, he, hB⟩ | ⟨hw, τ, ϖ, e, α, hU, he, hB, rfl⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    exact Or.inl ⟨hv, hB.2.2.1, fun j hj =>
      smul_left_injective ℂ hB.1 ((hc.split hx he hϖ hj).symm.trans (hB.2.2.2 ϖ hϖ j hj))⟩
  · exact Or.inr ⟨hw, τ, ϖ, α, hU, he.1, rfl, fun d t hd ht => smul_left_injective ℂ hB.1
      ((hc.inert hx he hU.2.2.2.1 hd ht).symm.trans (hB.2.2 _ (Final.DosetIndMem _ _ ℂ t)))⟩

theorem IsEigenSys.isParamVec (hc : IsEigenSys σ J L h ρ x c) (h0 : x ≠ 0) (hx : x ∈ fixed ρ (stabLoc σ J L v))
    (hs : IsSplit (E := E) v → ∃ e, IsSplitChart σ J L h e)
    (hi : IsInertAt F E v w → ∀ τ, IsConjAt σ h τ → ∃ e, IsInertChart σ J L h τ e)
    (hB : IsSysParam σ n h c B) : IsParamVec σ J L h ρ x B := by
  rcases hB with ⟨hv, h1, h2⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, h2⟩
  · obtain ⟨e, he⟩ := hs hv
    exact Or.inl ⟨hv, e, he, h0, (mem_fixed_comp_symm e he.2).2 hx, h1, fun ϖ hϖ j hj => by
      rw [hc.split hx he hϖ hj, h2 j hj]⟩
  · obtain ⟨e, he⟩ := hi hw τ hτ
    exact Or.inr ⟨hw, τ, ϖ, e, α, hU, he, isSatVecU_of_diag hU h0 ((mem_fixed_comp_symm e he.2.2).2 hx)
      fun d t hd ht => by rw [hc.inert hx he hU.2.2.2.1 hd ht, h2 d t hd ht], rfl⟩

end Place

end GlobalTheory.LFun

end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TripleIntertwiner

variable (D : D7) (T : Tor D) {N N' : ℕ}

theorem hf_add_left (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  unfold Hf
  rw [← add_div]
  congr 1
  simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_conj (x y : VC D N N') : Hf D T x y = (starRingEnd ℂ) (Hf D T y x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

def wLin (x : VC D N N') : (VC D N N' → ℂ) →ₗ[ℂ] (VC D N N' → ℂ) where
  toFun := Wd D T x
  map_add' F G := by funext z; simp only [Wd, U, Pi.add_apply]; ring
  map_smul' a F := by funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def cocExp (x y : VC D N N') : ℂ :=
  (Real.pi : ℂ) * (Hf D T y x - Hf D T x y) / 2 -
    (Real.pi : ℂ) * Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ) / 2 *
      (((Hf D T x y).re : ℂ) + ((Hf D T y x).re : ℂ))

theorem wLin_heis :
    (∀ (x y : VC D N N') f, wLin D T x (wLin D T y f) = Complex.exp (cocExp D T x y) • wLin D T (x + y) f) ∧
    (∀ x x' y : VC D N N', Complex.exp (cocExp D T (x + x') y) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x' y)) ∧
    (∀ x y y' : VC D N N', Complex.exp (cocExp D T x (y + y')) =
      Complex.exp (cocExp D T x y) * Complex.exp (cocExp D T x y')) ∧
    ∀ x y : VC D N N', Complex.exp (cocExp D T x y) ≠ 0 := by
  refine ⟨fun x y f => ?_, fun x x' y => ?_, fun x y y' => ?_, fun _ _ => Complex.exp_ne_zero _⟩
  · funext z
    show Wd D T x (Wd D T y f) z = Complex.exp (cocExp D T x y) * Wd D T (x + y) f z
    simp only [Wd, U, wdPh, ee, qH, add_assoc]
    have : ∀ a b c d e g h u : ℂ, a + b + c + d = e + g + h →
        Complex.exp a * (Complex.exp b * (u * Complex.exp c) * Complex.exp d) =
          Complex.exp e * (Complex.exp g * (u * Complex.exp h)) := by
      intro a b c d e g h u hh
      calc _ = u * Complex.exp (a + b + c + d) := by simp only [Complex.exp_add]; ring
        _ = _ := by rw [hh]; simp only [Complex.exp_add]; ring
    apply this
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring
  · rw [← Complex.exp_add]; congr 1
    simp only [cocExp, hf_add_left, hf_add_right, Complex.add_re]
    push_cast
    ring

theorem im_int_of_comm (x v : VC D N N')
    (h : Complex.exp (cocExp D T x v) = Complex.exp (cocExp D T v x)) : ∃ m : ℤ, (Hf D T v x).im = m := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨m, ?_⟩
  have h1 : Hf D T v x - Hf D T x v = 2 * ((Hf D T v x).im : ℂ) * Complex.I := by
    rw [hf_conj D T x v, Complex.sub_conj]; push_cast; ring
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((Hf D T v x).im : ℂ) = (2 * (Real.pi : ℂ) * Complex.I) * m := by
    simp only [cocExp] at hm
    linear_combination hm - (Real.pi : ℂ) * h1
  have h3 := mul_left_cancel₀ Complex.two_pi_I_ne_zero h2
  exact_mod_cast h3

theorem iop_eq_itw (A B : AddSubgroup (VC D N N'))
    (hB : ∀ x ∈ B, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) (G : VC D N N' → ℂ) :
    Iop D T A B G = itw (wLin D T) A B G := by
  funext z
  simp only [Iop, itw, Pi.smul_apply, smul_eq_mul]
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    exact (congrFun (hB _ (rep_mem q) G) z).symm

theorem itw_smul {V F : Type} [AddCommGroup V] [AddCommGroup F] [Module ℂ F] (W : V → F →ₗ[ℂ] F)
    (A B : AddSubgroup V) (a : ℂ) (f : F) : itw W A B (a • f) = a • itw W A B f := by
  by_cases h : (A.addSubgroupOf B).index = 0
  · simp [itw, h]
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    simp only [itw, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]
    rw [smul_comm]

theorem triple_constant : ∀ D : D7, GaussSumTripleConstant D := by
  intro D cc δ hc N N' A B C kA kB kC th hth
  by_cases h0 : th = 0
  · refine ⟨1, one_pow _, ?_⟩
    subst h0
    have e : ∀ X Y : AddSubgroup (VC D N N'), Iop D (tor0 D cc δ) X Y 0 = 0 := by
      intro X Y; funext z; simp [Iop, U]
    rw [e, e, e]; funext z; simp
  set T := tor0 D cc δ with hT
  have line := fun X (k : KLat D T X) => GlobalTheory.T.theta_space_selfDual_pair_at_most_line D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ hc N N' X k
  have eqI : ∀ X Y : AddSubgroup (VC D N N'), KLat D T Y → ∀ G, Iop D T X Y G = itw (wLin D T) X Y G :=
    fun X Y k G => iop_eq_itw D T X Y (line Y k).2.1 G
  have fix : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ G ∈ ThSp D T X, ∀ x ∈ X, wLin D T x G = G := by
    intro X k G hG x hx
    show Wd D T x G = G
    rw [(line X k).2.1 x hx]
    funext z
    exact hG.2 x hx z
  have uni : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X,
      itw (wLin D T) X Y G ∈ ThSp D T Y ∧ itw (wLin D T) Y X (itw (wLin D T) X Y G) = G := by
    intro X Y kX kY G hG
    have := GlobalTheory.T.intertwinerUnitary_all D cc δ hc N N' X Y kX kY G hG
    rw [← eqI X Y kY, ← eqI Y X kX]
    exact ⟨this.2.1, this.2.2.2⟩
  have nz : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → ∀ G ∈ ThSp D T X, G ≠ 0 →
      itw (wLin D T) X Y G ≠ 0 := by
    intro X Y kX kY G hG hG0 h
    have := (uni X Y kX kY G hG).2
    rw [h, ← zero_smul ℂ (0 : VC D N N' → ℂ), itw_smul, zero_smul] at this
    exact hG0 this.symm
  have ex : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∃ G ∈ ThSp D T X, G ≠ 0 :=
    fun X k => ⟨_, (uni A X kA k th hth).1, nz A X kA k th hth h0⟩
  have fin : ∀ X Y : AddSubgroup (VC D N N'), KLat D T X → KLat D T Y → X.relIndex Y ≠ 0 := by
    intro X Y kX kY h
    obtain ⟨G, hG, hG0⟩ := ex X kX
    apply nz X Y kX kY G hG hG0
    have h' : (X.addSubgroupOf Y).index = 0 := h
    simp [itw, h']
  have fin3 : ∀ Y : AddSubgroup (VC D N N'), KLat D T Y → (A ⊓ B ⊓ C).relIndex Y ≠ 0 := fun Y k =>
    AddSubgroup.relIndex_inf_ne_zero (AddSubgroup.relIndex_inf_ne_zero (fin A Y kA k) (fin B Y kB k))
      (fin C Y kC k)
  have H := wLin_heis D T (N := N) (N' := N')
  have coc : ∀ X : AddSubgroup (VC D N N'), KLat D T X → ∀ x ∈ X, ∀ y ∈ X,
      Complex.exp (cocExp D T x y) = 1 := by
    intro X k x hx y hy
    obtain ⟨G, hG, hG0⟩ := ex X k
    have := H.1 x y G
    rw [fix X k G hG y hy, fix X k G hG x hx, fix X k G hG _ (X.add_mem hx hy)] at this
    exact smul_left_injective ℂ hG0 (this.symm.trans (one_smul ℂ G).symm)
  have m1 := (uni A B kA kB th hth).1
  have m2 := (uni B C kB kC _ m1).1
  have m3 := (uni A C kA kC th hth).1
  have m4 := (uni C B kC kB _ m3).1
  obtain ⟨μ, μ', h4, e1, e2⟩ := itw_triple (c := fun x y => Complex.exp (cocExp D T x y)) H
    (fin3 A kA) (fin3 B kB) (fin3 C kC) (coc A kA) (coc B kB) (coc C kC)
    (fun v hv => (line A kA).2.2.2.1 v fun y hy => im_int_of_comm D T y v (hv y hy))
    th (fix A kA th hth) (fix B kB _ m1) (fix C kC _ m2) (fix C kC _ m3) (fix B kB _ m4)
  have e3 := (uni C A kC kA _ m2).2
  rw [e1, itw_smul] at e3
  have e4 := (uni B C kB kC _ m1).2
  have e5 := (uni A B kA kB th hth).2
  rw [← e4, ← e3, itw_smul, itw_smul, e2, smul_smul] at e5
  have e6 : μ * μ' = 1 := smul_left_injective ℂ h0 (e5.trans (one_smul ℂ th).symm)
  refine ⟨μ, ?_, ?_⟩
  · calc μ ^ 8 = μ ^ 4 * μ ^ 4 := by ring
      _ = (μ * μ') ^ 4 := by rw [mul_pow, ← h4]
      _ = 1 := by rw [e6, one_pow]
  · rw [eqI B C kC, eqI A B kB, eqI A C kC, ← e3]
    rfl

end GlobalTheory.TripleIntertwiner
end
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V
open scoped Matrix TensorProduct

namespace GlobalTheory.SlTwoCusp

open Topology

theorem continuous_pInf' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  exact hc.comp continuous_fst

theorem continuous_of_isOpen_stab : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a),
    IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1 := by
  intro F _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA F a => g⁻¹ * x := continuous_const.mul continuous_id
  have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F a → GL (Fin a) (TR.Rinf F)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf' F))
  have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F a → GL (Fin a) (Af F)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  have h1 : Continuous fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp (hI.comp hm)
  have h2 : ContinuousAt (fun x : GA F a => TR.chart φ.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
      (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA F a | TR.finRep F a (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage (hFn.comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [TR.chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * TR.infGL F a _ * finGL F a _) = _
  rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]

open MeasureTheory Topology

end GlobalTheory.SlTwoCusp
end
