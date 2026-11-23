module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle098
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT

theorem finite_quot_divLat_mulLat_homAt :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (cA c : ℕ), Submodule.IsLattice E N → Submodule.IsLattice E N' → 0 < cA → 0 < c → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  by
  intro E _ _ _ a b S N N' cA cB hN hN' hA hB
  classical
  obtain ⟨G, hG⟩ := hN.fg
  have hA' : (cA : E) ≠ 0 := by exact_mod_cast hA.ne'
  have hB' : (cB : E) ≠ 0 := by exact_mod_cast hB.ne'
  have memD : ∀ x : HomE E a b, x ∈ divLat cA (homAt S N N') ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, (cA : 𝓞 E) • x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  have memM : ∀ x : HomE E a b, x ∈ mulLat cB (homAt S N N') ↔
      ∃ h ∈ homAt S N N', (cB : 𝓞 E) • h = x := fun x => Iff.rfl
  have memH : ∀ x : HomE E a b, x ∈ homAt S N N' ↔
      ∀ P ∈ S, ∀ y ∈ localization₂ P.asIdeal N, x y ∈ localization₂ P.asIdeal N' := fun x => Iff.rfl
  let ev : HomE E a b →ₗ[𝓞 E] (G → Sp E b) :=
    { toFun := fun x g => (cA : 𝓞 E) • x g
      map_add' := by intro x y; funext g; simp
      map_smul' := by intro r x; funext g; simp [smul_comm r] }
  let T : Submodule (𝓞 E) (G → Sp E b) := Submodule.pi Set.univ fun _ => N'
  have hT : T.FG := Submodule.fg_pi fun _ => hN'.fg
  let Z : Submodule (𝓞 E) (HomE E a b) := T.comap ev
  have memZ : ∀ x : HomE E a b, x ∈ Z ↔ ∀ g : G, (cA : 𝓞 E) • x g ∈ N' := fun x =>
    ⟨fun h g => h g trivial, fun h g _ => h g⟩
  have hZD : Z ≤ divLat cA (homAt S N N') := by
    intro x hx
    rw [memD]
    intro P hP y hy
    obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
    have : ∀ w ∈ N, (cA : 𝓞 E) • x w ∈ N' := by
      intro w hw
      rw [← hG] at hw
      induction hw using Submodule.span_induction with
      | mem g hg => exact (memZ x).1 hx ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => rw [map_add (f := _), smul_add]; exact N'.add_mem hu hv
      | smul r u _ hu => rw [LinearMap.map_smul_of_tower, smul_comm]; exact N'.smul_mem r hu
    refine (mem_locP P N' _).2 ⟨s, hs, ?_⟩
    have h := this _ hsy
    rwa [LinearMap.map_smul_of_tower, smul_comm] at h
  have hc : ((cB : 𝓞 E) * cA) ≠ 0 := by
    have : cB * cA ≠ 0 := by positivity
    exact_mod_cast this
  have : Finite (𝓞 E ⧸ Ideal.span {(cB : 𝓞 E) * cA}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa [Ideal.span_singleton_eq_bot] using hc)
  have hsurj : Function.Surjective
      (((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD) := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    let I : Ideal (𝓞 E) := Z.comap (LinearMap.toSpanSingleton (𝓞 E) _ x)
    have hI : ∀ P ∈ S, ∃ s ∈ I, s ∉ P.asIdeal := by
      intro P hP
      have h1 : ∀ g : G, ∃ s ∉ P.asIdeal, s • (cA : 𝓞 E) • x g ∈ N' := fun g =>
        (mem_locP P N' _).1 ((memD x).1 hx P hP g (le_locP P N (hG ▸ Submodule.subset_span g.2)))
      choose f hf hf' using h1
      refine ⟨∏ g, f g, ?_, ?_⟩
      · show (∏ g, f g) • x ∈ Z
        rw [memZ]
        intro g
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ g), LinearMap.smul_apply, smul_comm, mul_smul]
        exact N'.smul_mem _ (hf' g)
      · intro h
        have := P.isPrime
        obtain ⟨g, _, hg⟩ := Ideal.IsPrime.prod_mem_iff.1 h
        exact hf g hg
    obtain ⟨s, hs, t, r, ht, htr⟩ := GlobalTheory.exists_mem_one_sub_loc_dvd S I hI ((cB : 𝓞 E) * cA)
    refine ⟨⟨s • x, hs⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show x - s • x ∈ mulLat cB (homAt S N N')
    have hBinv : ∀ {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] (w : W),
        (cB : 𝓞 E) • (cB : E)⁻¹ • w = w := by
      intro W _ _ _ w
      rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hB', one_smul]
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x - s • x), ?_, hBinv _⟩
    rw [memH]
    intro P hP y hy
    obtain ⟨u, hu, huy⟩ := (mem_locP P N' _).1 ((memD x).1 hx P hP y hy)
    refine (mem_locP P N' _).2 ⟨u * t, fun h => (P.isPrime.mem_or_mem h).elim hu (ht P hP), ?_⟩
    have e1 : t • ((cB : E)⁻¹ • (x - s • x)) y = r • (cA : 𝓞 E) • x y := by
      have e2 : (x - s • x) y = (1 - s) • x y := by simp [sub_smul]
      rw [LinearMap.smul_apply, smul_comm, e2, smul_smul t, htr, mul_assoc, mul_smul, smul_comm, hBinv, mul_comm, mul_smul]
    rw [mul_smul, e1, smul_comm]
    exact N'.smul_mem r huy
  let f : Z →ₗ[𝓞 E] T := ev.restrict (p := Z) (q := T) fun x hx => hx
  let q : Z →ₗ[𝓞 E] _ :=
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype).mkQ ∘ₗ Submodule.inclusion hZD
  have hk : LinearMap.ker f ≤ LinearMap.ker q := by
    intro x hx
    have hxg : ∀ g : G, (x : HomE E a b) g = 0 := by
      intro g
      have h := congrFun (congrArg Subtype.val (LinearMap.mem_ker.mp hx)) g
      have h2 : (cA : E) • (x : HomE E a b) g = 0 := by
        rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E)]
        exact h
      exact (smul_eq_zero.mp h2).resolve_left hA'
    have hxN : ∀ y ∈ N, (x : HomE E a b) y = 0 := by
      intro y hy
      rw [← hG] at hy
      induction hy using Submodule.span_induction with
      | mem g hg => exact hxg ⟨g, hg⟩
      | zero => simp
      | add u v _ _ hu hv => simp [hu, hv]
      | smul r u _ hu => simp [LinearMap.map_smul_of_tower, hu]
    have hxloc : ∀ (P : HeightOneSpectrum (𝓞 E)), ∀ y ∈ localization₂ P.asIdeal N, (x : HomE E a b) y = 0 := by
      intro P y hy
      obtain ⟨s, hs, hsy⟩ := (mem_locP P N y).1 hy
      have hs0 : (s : E) ≠ 0 := by
        intro h
        have : s = 0 := by exact_mod_cast h
        exact hs (this ▸ P.asIdeal.zero_mem)
      have h := hxN _ hsy
      rw [LinearMap.map_smul_of_tower] at h
      have h' : (s : E) • (x : HomE E a b) y = 0 := by
        exact h
      exact (smul_eq_zero.mp h').resolve_left hs0
    apply LinearMap.mem_ker.mpr
    change Submodule.Quotient.mk (Submodule.inclusion hZD x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change (x : HomE E a b) ∈ mulLat cB (homAt S N N')
    rw [memM]
    refine ⟨(cB : E)⁻¹ • (x : HomE E a b), ?_, ?_⟩
    · rw [memH]
      intro P hP y hy
      simp [hxloc P y hy]
    · ext y
      simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E,
        smul_smul, mul_inv_cancel₀ hB', one_smul]
  have : Module.Finite (𝓞 E) T := Module.Finite.iff_fg.2 hT
  have : Module.Finite (𝓞 E) (LinearMap.range f) := Module.Finite.of_injective
    (LinearMap.range f).subtype Subtype.val_injective
  have : Module.Finite (𝓞 E) (Z ⧸ LinearMap.ker f) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  let q' := (LinearMap.ker f).liftQ q hk
  have hq' : Function.Surjective q' := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk x, hx⟩
  have := Module.Finite.of_surjective q' hq' 
  have : Module.Finite ℤ (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
    Module.Finite.trans (𝓞 E) _
  refine Module.finite_of_fg_torsion _ ?_
  intro q
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine ⟨⟨((cB * cA : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
  rw [Submonoid.mk_smul, natCast_zsmul, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero]
  show ((cB * cA : ℕ) : 𝓞 E) • x ∈ mulLat cB (homAt S N N')
  rw [memM]
  exact ⟨(cA : 𝓞 E) • x, hx, by rw [smul_smul, Nat.cast_mul]⟩


end GlobalTheory.MomT
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory

theorem exists_reps_sup_of_finite_quot (E : Type) [Field E] (H : Type) [AddCommGroup H]
    [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H)
    (hfin : Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)) :
    ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧
      (∀ x ∈ R, ∀ y ∈ R, x - y ∈ Z₀.toAddSubgroup ⊔ C → x = y) ∧
      ∀ y ∈ Z₁, ∃ x ∈ R, y - x ∈ Z₀.toAddSubgroup ⊔ C := by
  classical
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  set Z : AddSubgroup H := Z₀.toAddSubgroup ⊔ C with hZ
  let s : (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → ↥Z₁ :=
    Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
  have hs : ∀ z, Submodule.Quotient.mk (s z) = z := fun z =>
    Function.surjInv_eq (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype)) z
  let T : Finset (H ⧸ Z) := Finset.univ.image fun z => QuotientAddGroup.mk (s z : H)
  have hsurj : (Z₁ : Set H).SurjOn (QuotientAddGroup.mk : H → H ⧸ Z) T := by
    intro t ht
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
    exact ⟨s z, (s z).2, rfl⟩
  obtain ⟨R, hR, hinj, him⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  refine ⟨R, fun x hx => hR hx, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hinj hx hy (QuotientAddGroup.eq_iff_sub_mem.2 hxy)
  · intro y hy
    have h1 : (⟨y, hy⟩ : ↥Z₁) - s (Submodule.Quotient.mk ⟨y, hy⟩) ∈ Z₀.comap Z₁.subtype :=
      (Submodule.Quotient.eq _).1 (hs _).symm
    have h2 : y - (s (Submodule.Quotient.mk ⟨y, hy⟩) : H) ∈ Z :=
      AddSubgroup.mem_sup_left (by simpa using h1)
    have h3 : (QuotientAddGroup.mk y : H ⧸ Z) ∈ T :=
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, (QuotientAddGroup.eq_iff_sub_mem.2 h2).symm⟩
    rw [← him] at h3
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 h3
    exact ⟨x, hx, QuotientAddGroup.eq_iff_sub_mem.1 hxy.symm⟩

theorem latSum_eq_sum_sum_reps : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (H : Type) [AddCommGroup H] [Module (𝓞 E) H] (Z₁ Z₀ : Submodule (𝓞 E) H) (C : AddSubgroup H) (J : Finset H), Z₀ ≤ Z₁ → C ≤ Z₁.toAddSubgroup → Finite (↥Z₁ ⧸ Z₀.comap Z₁.subtype) → IsReps Z₀.toAddSubgroup C J → ∃ R : Finset H, (∀ x ∈ R, x ∈ Z₁) ∧ ∀ (M : Type) [AddCommMonoid M] (f : H → M), (∀ x ∈ Z₁, ∀ y ∈ Z₀, f (x + y) = f x) → latSum Z₁ Z₀ f = ∑ x ∈ R, ∑ j ∈ J, f (x + j) := by
  intro E _ _ _ H _ _ Z₁ Z₀ C J h01 hC hfin hJ
  classical
  obtain ⟨R, hR, hRinj, hRsurj⟩ := exists_reps_sup_of_finite_quot E H Z₁ Z₀ C hfin
  obtain ⟨hJC, hJinj, hJsurj⟩ := hJ
  refine ⟨R, hR, ?_⟩
  intro M _ f hf
  letI := Fintype.ofFinite (↥Z₁ ⧸ Z₀.comap Z₁.subtype)
  have hmem : ∀ p ∈ R ×ˢ J, p.1 + p.2 ∈ Z₁ := fun p hp =>
    Z₁.add_mem (hR _ (Finset.mem_product.1 hp).1) (hC (hJC _ (Finset.mem_product.1 hp).2))
  unfold latSum
  rw [finsum_eq_sum_of_fintype, ← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun p hp => (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, j⟩ hp ⟨x', j'⟩ hp' h
    obtain ⟨hx, hj⟩ := Finset.mem_product.1 hp
    obtain ⟨hx', hj'⟩ := Finset.mem_product.1 hp'
    have h1 : x + j - (x' + j') ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h
    have h2 : x = x' := by
      refine hRinj x hx x' hx' ?_
      have : x - x' = (x + j - (x' + j')) + (j' - j) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup h1 (C.sub_mem (hJC _ hj') (hJC _ hj))
    subst h2
    have h3 : j = j' := by
      refine hJinj j hj j' hj' ?_
      have : j - j' = x + j - (x + j') := by abel
      rw [this]
      exact h1
    rw [h3]
  · intro z _
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨x, hx, hyx⟩ := hRsurj y hy
    obtain ⟨a, ha, c, hc, hac⟩ := AddSubgroup.mem_sup.1 hyx
    obtain ⟨j, hj, hcj⟩ := hJsurj c hc
    refine ⟨(x, j), Finset.mem_product.2 ⟨hx, hj⟩, (Submodule.Quotient.eq _).2 ?_⟩
    have h1 : x + j - y = -(a + (c - j)) := by
      have : y = x + (a + c) := by rw [hac]; abel
      rw [this]; abel
    have h2 : x + j - y ∈ Z₀ := by
      rw [h1]
      exact Z₀.neg_mem (Z₀.add_mem ha hcj)
    simpa using h2
  · intro p hp
    set w := Function.surjInv (Submodule.Quotient.mk_surjective (Z₀.comap Z₁.subtype))
      (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩) with hw
    have h0 : Submodule.Quotient.mk w =
        (Submodule.Quotient.mk ⟨p.1 + p.2, hmem p hp⟩ : ↥Z₁ ⧸ Z₀.comap Z₁.subtype) :=
      Function.surjInv_eq _ _
    have h1 : (w : H) - (p.1 + p.2) ∈ Z₀ := by
      simpa using (Submodule.Quotient.eq _).1 h0
    have h2 := hf _ (hmem p hp) _ h1
    rw [← h2]
    congr 1
    abel

end GlobalTheory
end

section

noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.KapSplitNorm

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one (q : ℕ) [Fact q.Prime] (n : ℕ) (hn : ¬ q ∣ n) : ‖((n : ℕ) : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (n : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)

theorem norm_iota_le_one (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int (ι : ℂ →+* ℂ_[q]) hz using 1 <;> first | exact Subsingleton.elim _ _ | rfl)

theorem norm_iota_unit (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (hn : ¬ q ∣ n) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (n : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := norm_iota_le_one q ι x hx
  have e2 := norm_iota_le_one q ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, map_natCast, norm_natCast_eq_one q n hn]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt_eq_one {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpq : p ≠ q) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpq' : ¬ q ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow h
    exact hpq (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa_split : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q →
    ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  intro D γ₀ k q _ hsq ι
  have hfin := yFinite D γ₀ k
  have hfinS : (Function.mulSupport
      (fun p : {p : ℕ // p.Prime ∧ SplitK D p} => k.rt p ^ (-(k.yP p)))).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro p hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    intro h0
    apply hp
    simp [h0]
  let F : ℂ →* ℝ :=
    { toFun := fun z => ‖ι z‖
      map_one' := by simp
      map_mul' := fun x y => by simp [norm_mul] }
  have hF : ∀ z, F z = ‖ι z‖ := fun _ => rfl
  rw [KapChoice.kappa, ← hF, MonoidHom.map_finprod F hfinS,
    finprod_eq_single _ (⟨q, Fact.out, hsq⟩ : {p : ℕ // p.Prime ∧ SplitK D p})]
  · rw [hF, map_zpow₀, norm_zpow]
  · intro p hp
    have hpq : (p : ℕ) ≠ q := fun h => hp (Subtype.ext h)
    rw [hF, map_zpow₀, norm_zpow, norm_rt_eq_one k q ι p p.2.1 p.2.2 hpq, one_zpow]

end GlobalTheory.KapSplitNorm
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomPlace

theorem norm_le_one_of_isIntegral_int {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem exists_extension (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (σ : K →+* ℂ) (ι : K →+* ℂ_[p]) :
    ∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k := by
  have hmem : ∀ k, σ k ∈ TaylorLogMetric.Qbar := fun k =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom σ.toRatAlgHom)
  let σ' : K →+* TaylorLogMetric.Qbar := σ.codRestrict TaylorLogMetric.Qbar hmem
  let : Algebra K TaylorLogMetric.Qbar := σ'.toAlgebra
  let : Algebra K ℂ_[p] := ι.toAlgebra
  have : IsScalarTower ℚ K TaylorLogMetric.Qbar := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast, eq_ratCast, map_ratCast]
  have : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar := by
    convert algebraicClosure.isAlgebraic ℚ ℂ <;> first | rfl | exact Subsingleton.elim _ _
  have : Algebra.IsAlgebraic K TaylorLogMetric.Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  let f : TaylorLogMetric.Qbar →ₐ[K] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun k => ⟨hmem k, ?_⟩⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left (hmem k)]
  exact f.commutes k

theorem norm_le_one_of_valuation (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]
    (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖ι x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hint : ∀ y : 𝓞 K, ‖ι (y : K)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (by
      convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖ι x‖ * ‖ι ((d : 𝓞 K) : K)‖ = ‖ι (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖ι z‖) h
  have h3 := hint n
  nlinarith [norm_nonneg (ι x)]

theorem exp_rat_pow_den (r : ℚ) :
    Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ^ r.den = 1 := by
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨-r.num, ?_⟩
  have h : ((r.den : ℂ)) * (r : ℂ) = (r.num : ℂ) := by
    exact_mod_cast Rat.den_mul_eq_num r
  push_cast
  rw [← h]; ring

theorem root_of_unity_norm {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : z ^ n = 1) : z ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam z‖ = 1 := by
  have hmem : z ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (Nat.pos_of_ne_zero hn) ?_)
    rw [hz]; exact isAlgebraic_one
  refine ⟨hmem, ?_⟩
  unfold TaylorLogMetric.lamC
  rw [dite_eq_left hmem]
  have h1 : (⟨z, hmem⟩ : TaylorLogMetric.Qbar) ^ n = 1 := Subtype.ext (by simpa using hz)
  have h2 : ‖lam ⟨z, hmem⟩‖ ^ n = 1 := by rw [← norm_pow, ← map_pow, h1, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 h2

theorem places : ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (σ : K →+* ℂ) (ι : K →+* ℂ_[p]), (∃ lam : TaylorLogMetric.Qbar →+* ℂ_[p], ∀ k, σ k ∈ TaylorLogMetric.Qbar ∧ TaylorLogMetric.lamC lam (σ k) = ι k) ∧ (∀ w : HeightOneSpectrum (𝓞 K), (∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) → ∀ x : K, w.valuation K x ≤ 1 → ‖ι x‖ ≤ 1) ∧ ∀ (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (r : ℚ), Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * ((r : ℝ) : ℂ)))‖ = 1 :=
  fun K _ _ p _ σ ι => ⟨exists_extension K p σ ι, norm_le_one_of_valuation K p ι,
    fun lam r => root_of_unity_norm lam r.den_ne_zero (exp_rat_pow_den r)⟩

end GlobalTheory.MomPlace
end
