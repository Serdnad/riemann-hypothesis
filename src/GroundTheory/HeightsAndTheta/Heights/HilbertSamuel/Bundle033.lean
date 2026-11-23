module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.Bundle001
public import Mathlib.Algebra.Order.PUnit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle005
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionsSeparated

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mem_mCoordIdeal_of_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero,
    zero_mul]

def IsRepAt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧
    aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0

theorem rep_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {g h g' h' : MRing ι} (hr : IsRepAt y a τ s z g h)
    (hr' : IsRepAt y a τ s z g' h') :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy, -⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', -⟩ := hr'
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have : ((dg k + dh' k : ℕ) : ℤ) = ((dg' k + dh k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  have hF : IsMultiHomog (g * h' - g' * h) (dg + dh') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [hdeg]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := hz.2 _ (mem_mCoordIdeal_of_homog y hF h0)
  simp only [map_sub, map_mul] at this
  exact sub_eq_zero.mp this

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {g h g' h' : MRing ι}
    (hr : IsRepAt y a τ s z g h) (hr' : IsRepAt y a τ t z g' h') :
    IsRepAt y a τ (s + t) z (g * h' + g' * h) (h * h') := by
  obtain ⟨dg, dh, hg, hh, hd, hy, hz0⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', hz0'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  refine ⟨dg + dh', dh + dh', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact isMultiHomog_mul hg' hh
  · intro k
    simp only [Pi.add_apply]
    push_cast
    linarith [hd k]
  · rw [map_add (f := _), map_mul, map_mul, map_mul, hy, hy']
    ring
  · simp only [map_mul]
    exact mul_ne_zero hz0 hz0'

end SmallSectionsSeparated


open SmallSectionsSeparated in
theorem SmallSectionsSeparated.proof (hG : GridSeparation.Statement) : SmallSectionsSeparated.Statement := by
  intro K _ ι _ Ω _ y D A hV hB hA
  obtain ⟨C, hC, hZ⟩ := hG K ι Ω y D A hV hB hA
  refine ⟨C, hC, fun τ => ?_⟩
  obtain ⟨Z, hZP, hrep, hsep⟩ := hZ τ
  classical
  have hR : ∀ (s : chartLatNm y A.a τ) (z : Z), ∃ gh : MRing ι × MRing ι,
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) gh.1 gh.2 := by
    intro s z
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz⟩ := hrep s s.2 z z.2
    exact ⟨(g, h), dg, dh, hg, hh, hd, hy, hz⟩
  choose gh hgh using hR
  let val : chartLatNm y A.a τ → Z → ℂ := fun s z =>
    eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).1) /
      eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).2)

  have hval : ∀ (s : chartLatNm y A.a τ) (z : Z) (g h : MRing ι),
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) g h →
      val s z = eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g) /
        eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) := by
    intro s z g h hr
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := hr.choose_spec.choose_spec.2.2.2.2
    rw [div_eq_div_iff h1 h2]
    exact rep_cross (hZP z z.2) (hgh s z) hr
  let ev : chartLatNm y A.a τ →+ (Z → ℂ) := AddMonoidHom.mk' (fun s z => val s z) (by
    intro s t
    funext z
    have hst := rep_add (hgh s z) (hgh t z)
    rw [Pi.add_apply, hval (s + t) z _ _ (by simpa using hst)]
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := (hgh t z).choose_spec.choose_spec.2.2.2.2
    simp only [val, map_add (f := _), map_mul]
    field_simp)
  refine ⟨Z, ev, hZP, ?_, ?_⟩
  · intro s z
    obtain ⟨dg, dh, hg, hh, hd, hy, hz⟩ := hgh s z
    refine ⟨dg, dh, (gh s z).1, (gh s z).2, hg, hh, hd, hy, hz, ?_⟩
    show val s z * _ = _
    simp only [val]
    exact div_mul_cancel₀ _ hz
  · intro s t _ _ hst
    have hu : ((s - t : chartLatNm y A.a τ) : Ω) ≠ 0 := by
      intro h0
      exact hst (sub_eq_zero.mp (Subtype.ext h0))
    obtain ⟨z, hzZ, dg, dh, g, h, hg, hh, hd, hy, hz, hb⟩ := hsep _ (s - t).2 hu
    refine ⟨⟨z, hzZ⟩, ?_⟩
    have hev : ev s ⟨z, hzZ⟩ - ev t ⟨z, hzZ⟩ = val (s - t) ⟨z, hzZ⟩ := by
      rw [← Pi.sub_apply, ← map_sub]
      rfl
    rw [hev, hval (s - t) ⟨z, hzZ⟩ g h ⟨dg, dh, hg, hh, hd, hy, hz⟩, norm_div]
    rw [le_div_iff₀ (norm_pos_iff.mpr hz)]
    exact hb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Trivial

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]


omit [Fintype K] [LinearOrder K] [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] in
theorem loc_subsingleton_of_kill {T : Submonoid (MRingOver S ι)} {u : MRingOver S ι} (hu : u ∈ T)
    (hk : ∀ y : M, u • y = 0) : Subsingleton (LocalizedModule T M) := by
  have h0 : ∀ x : LocalizedModule T M, x = 0 := by
    intro x
    induction x using LocalizedModule.induction_on with
    | h y s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.mpr ⟨⟨u, hu⟩, ?_⟩
      simp only [Submonoid.smul_def, smul_zero]
      rw [smul_comm, hk, smul_zero]
  exact ⟨fun a b => by rw [h0 a, h0 b]⟩

theorem h1_vanish_generated_of_localized_subsingleton
    (h : ∀ (n : ℕ) (I : KH.Cell K ι n), Subsingleton (LocalizedModule (KH.cellMon S I.1) M))
    (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) :
    Subsingleton (KH.cechHc ι 𝓜 d 1) ∧ GeneratedMod S ι 𝓜 d := by
  have : Subsingleton (KH.CechC S ι M 1) := ⟨fun f g => funext fun I => (h 1 I).elim _ _⟩
  refine ⟨⟨fun x y => ?_⟩, fun I x _ => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]
  · refine ⟨1, 0, 0, Fin.elim0, Fin.elim0, Submonoid.one_mem _, isMultiHomog_one_zero, fun j => j.elim0,
      fun j => j.elim0, ?_⟩
    rw [one_smul, Fin.sum_univ_zero]
    exact (h 0 I).elim _ _


omit [LinearOrder K] [∀ k, LinearOrder (ι k)] in
theorem isMGraded_punit : KH.IsMGraded S ι (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) := by
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (fun _ => disjoint_bot_left)
    (Subsingleton.elim _ _), fun _ _ _ _ _ _ => (Submodule.mem_bot _).2 (Subsingleton.elim _ _)⟩

end Trivial

theorem H1GenerationDevissage.proof (hPF : KH.PrimeFiltStatement) (hSES : KH.CechSESStatement)
    (hGQ : GradedSubquot.Statement) (hGS : GenSESStep.Statement) : H1GenerationDevissage.Statement := by
  intro S _ K _ _ ι _ _ V N hS hP M _ _ _ _ 𝓜 hfin hgr hV e
  obtain ⟨r, m, c, 𝔭, hm, h𝔭, hcol, hspan⟩ := hPF S K ι M 𝓜 hS hfin hgr
  let G : ℕ → Set M := fun j => m '' {l | (l : ℕ) < j}
  let F : ℕ → Submodule (MRingOver S ι) M := fun j => Submodule.span _ (G j)
  have hGh : ∀ j, ∀ x ∈ G j, ∃ c', x ∈ 𝓜 c' := by
    rintro j _ ⟨l, -, rfl⟩
    exact ⟨c l, hm l⟩
  have hFmono : ∀ {i j : ℕ}, i ≤ j → F i ≤ F j := fun hij =>
    Submodule.span_mono (Set.image_mono fun l (hl : (l : ℕ) < _) => lt_of_lt_of_le hl hij)
  have hgrF : ∀ j, KH.IsMGraded S ι (subGrading 𝓜 (F j)) := fun j =>
    (hGQ S K ι M 𝓜 (G j) (G j) hgr (hGh j) (hGh j) le_rfl).1
  have key : ∀ j ≤ r, ∃ c₁ : ℕ, ∀ n : ℕ, c₁ ≤ n →
      Subsingleton (KH.cechHc ι (subGrading 𝓜 (F j)) (e + n • N) 1) ∧
        GeneratedMod S ι (subGrading 𝓜 (F j)) (e + n • N) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hF0 : F 0 = ⊥ := by simp [F, G]
      refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton
        (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun y => ?_) _ _⟩
      rw [one_smul]
      have hy : (y : M) ∈ (⊥ : Submodule (MRingOver S ι) M) := by
        rw [← hF0]
        exact y.2
      exact Submodule.coe_eq_zero.mp ((Submodule.mem_bot _).1 hy)
    | succ j ih =>
      intro hj
      obtain ⟨c₀, hc₀⟩ := ih (Nat.le_of_succ_le hj)
      let l : Fin r := ⟨j, hj⟩
      let L : Submodule (MRingOver S ι) (F (j + 1)) := (F j).comap (F (j + 1)).subtype
      have hq := (hGQ S K ι M 𝓜 (G j) (G (j + 1)) hgr (hGh j) (hGh (j + 1)) (hFmono (Nat.le_succ j))).2
      have hcolj : ∀ p : MRingOver S ι, p • m l ∈ F j ↔ p ∈ 𝔭 l := fun p => hcol l p
      have hkill : ∀ p ∈ 𝔭 l, ∀ y ∈ F (j + 1), p • y ∈ F j := by
        intro p hp y hy
        induction hy using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨l', hl', rfl⟩ := hx
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with h | h
          · exact (F j).smul_mem p (Submodule.subset_span ⟨l', h, rfl⟩)
          · rw [show l' = l from Fin.ext h]
            exact (hcolj p).2 hp
        | zero => rw [smul_zero]; exact (F j).zero_mem
        | add x y _ _ hx hy => rw [smul_add]; exact (F j).add_mem hx hy
        | smul a x _ hx => rw [smul_comm]; exact (F j).smul_mem a hx
      have hann : 𝔭 l ≤ Module.annihilator (MRingOver S ι) (F (j + 1) ⧸ L) := by
        intro p hp
        rw [Module.mem_annihilator]
        intro q
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective L q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        show ((p • y : F (j + 1)) : M) ∈ F j
        rw [Submodule.coe_smul]
        exact hkill p hp y y.2
      have hfinQ : Module.Finite (MRingOver S ι) (F (j + 1) ⧸ L) := by
        have : Module.Finite (MRingOver S ι) (F (j + 1)) :=
          Module.Finite.iff_fg.2 (Submodule.fg_span ((Set.toFinite _).image m))
        infer_instance
      obtain ⟨c₂, hc₂⟩ : ∃ c₂ : ℕ, ∀ n : ℕ, c₂ ≤ n →
          Subsingleton (KH.cechHc ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) 1) ∧
            GeneratedMod S ι (quotGrading (subGrading 𝓜 (F (j + 1))) L) (e + n • N) := by
        by_cases hrel : IsMultiProjPrime (𝔭 l)
        · exact hP (𝔭 l) hrel (hV.trans (h𝔭 l).2.2) (F (j + 1) ⧸ L) _ hfinQ hq hann e
        · have hirr : ¬ IsRelevant (𝔭 l) := fun h => hrel ⟨(h𝔭 l).1, (h𝔭 l).2.1, h⟩
          simp only [IsRelevant, not_forall, not_exists, not_not] at hirr
          obtain ⟨k, hk⟩ := hirr
          refine ⟨0, fun n _ => h1_vanish_generated_of_localized_subsingleton (fun _ I => ?_) _ _⟩
          obtain ⟨i, hi⟩ := I.2.1 k
          exact loc_subsingleton_of_kill (Submonoid.subset_closure ⟨k, i, hi, rfl⟩)
            (Module.mem_annihilator.1 (hann (hk i)))
      refine ⟨max c₀ c₂, fun n hn => ?_⟩
      have h0 := hc₀ n (le_of_max_le_left hn)
      have h2 := hc₂ n (le_of_max_le_right hn)
      let g := Submodule.inclusion (hFmono (Nat.le_succ j))
      have hex : LinearMap.range g = LinearMap.ker L.mkQ := by
        rw [Submodule.range_inclusion, Submodule.ker_mkQ]
      have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F j)) (subGrading 𝓜 (F (j + 1))) g := fun _ _ hx => hx
      have hhG : KH.IsMGradedMap S ι (subGrading 𝓜 (F (j + 1))) (quotGrading (subGrading 𝓜 (F (j + 1))) L)
          L.mkQ := fun _ _ hx => Submodule.mem_map_of_mem hx
      have H := hSES S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex (e + n • N) 1
      exact ⟨H.1 h0.1 h2.1, hGS S K ι _ _ _ _ _ _ g L.mkQ (hgrF j) (hgrF (j + 1)) hq hgG hhG
        (Submodule.inclusion_injective _) (Submodule.mkQ_surjective _) hex _ h0.1 h0.2 h2.2⟩
  have hFr : F r = ⊤ := by
    rw [← hspan]
    simp [F, G]
  obtain ⟨c₁, hc₁⟩ := key r le_rfl
  refine ⟨c₁, fun n hn => ?_⟩
  obtain ⟨h1, hgen⟩ := hc₁ n hn
  let g := (F r).subtype
  have hex : LinearMap.range g = LinearMap.ker (0 : M →ₗ[MRingOver S ι] PUnit) := by
    rw [Submodule.range_subtype, hFr, LinearMap.ker_zero]
  have hgG : KH.IsMGradedMap S ι (subGrading 𝓜 (F r)) 𝓜 g := fun _ _ hx => hx
  have hhG : KH.IsMGradedMap S ι 𝓜 (fun _ : K → ℤ => (⊥ : Submodule S PUnit)) 0 :=
    fun _ _ _ => Submodule.zero_mem _
  have hU := h1_vanish_generated_of_localized_subsingleton (M := PUnit) (S := S) (ι := ι)
    (fun _ _ => loc_subsingleton_of_kill (Submonoid.one_mem _) fun _ => Subsingleton.elim _ _)
    (fun _ => ⊥) (e + n • N)
  have H := hSES S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex (e + n • N) 1
  exact ⟨H.1 h1 hU.1, hGS S K ι _ M PUnit _ 𝓜 _ g 0 (hgrF r) hgr isMGraded_punit hgG hhG
    (Submodule.injective_subtype _) (fun _ => ⟨0, Subsingleton.elim _ _⟩) hex _ h1 hgen hU.2⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  set_option synthInstance.maxHeartbeats 200000 in
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage


open ProjFrameImage in
theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ K : ℝ, ∀ a b : ℕ, |twoBlockStep x (matAct B x) a b| ≤ K * ((a + b : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepLocal.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x (matAct B x) m m' D i *
            ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)))| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
