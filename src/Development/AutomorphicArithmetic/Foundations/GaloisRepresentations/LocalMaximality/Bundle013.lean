module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem fixLoc_key (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L)
    (e : B →ₐ[ℂ] ℂ) {d : ℕ} (g : Fin d → Fin d → L) (A : Matrix (Fin d) (Fin d) ℂ) (t r : Fin d → L)
    (hg : ∀ m l, Val B e (g m l) (A m l)) (hdet : (1 - A).det ≠ 0)
    (hr : ∀ a, r a = t a - ∑ l, g a l * t l) :
    ∃ N : Matrix (Fin d) (Fin d) L, (∀ a l, N a l ∈ loc B e) ∧ Val B e N.det (1 - A).det ∧
      (∀ a, r a = ∑ l, N a l * t l) ∧ ∀ l, InSp (loc B e) r (t l) := by
  obtain ⟨-, ⟨ev, hev⟩, -, hinv⟩ := hV L B e
  have hg' : ∀ m l, ∃ h : g m l ∈ loc B e, ev ⟨_, h⟩ = A m l := fun m l => (hev _ _).1 (hg m l)
  choose hmem hval using hg'
  let G : Matrix (Fin d) (Fin d) (loc B e) := fun m l => ⟨g m l, hmem m l⟩
  let N' : Matrix (Fin d) (Fin d) (loc B e) := 1 - G
  let ι : loc B e →+* L := (loc B e).val.toRingHom
  let ε : loc B e →+* ℂ := ev.toRingHom
  have hN'ε : ε.mapMatrix N' = 1 - A := by
    ext a l
    simp only [N', RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, map_sub]
    have h1 : ε ((1 : Matrix (Fin d) (Fin d) (loc B e)) a l) = (1 : Matrix (Fin d) (Fin d) ℂ) a l := by
      by_cases h : a = l
      · subst h; simp
      · simp [Matrix.one_apply_ne h]
    rw [h1]
    congr 1
    exact hval a l
  have hN : (ι.mapMatrix N').det = ι N'.det := (RingHom.map_det ι N').symm
  have hVal : Val B e (ι.mapMatrix N').det (1 - A).det := by
    rw [hN]
    refine (hev _ _).2 ⟨N'.det.2, ?_⟩
    have : ε N'.det = (1 - A).det := by rw [RingHom.map_det, hN'ε]
    exact this
  have hmul : ∀ a, r a = ∑ l, (ι.mapMatrix N') a l * t l := by
    intro a
    rw [hr a]
    have h2 : ∀ l, (ι.mapMatrix N') a l * t l = (if a = l then t l else 0) - g a l * t l := by
      intro l
      have h0 : (ι.mapMatrix N') a l = (if a = l then 1 else 0) - g a l := by
        show ι ((1 - G) a l) = _
        rw [Matrix.sub_apply, map_sub, Matrix.one_apply, apply_ite ι, map_one, map_zero]
        rfl
      rw [h0, sub_mul, ite_mul, one_mul, zero_mul]
    simp only [h2, Finset.sum_sub_distrib]
    simp
  refine ⟨ι.mapMatrix N', fun a l => (N' a l).2, hVal, hmul, fun l => ?_⟩
  obtain ⟨hv0, hvi⟩ := hinv _ _ hVal hdet
  refine ⟨fun a => ((ι.mapMatrix N').det)⁻¹ * (ι.mapMatrix N').adjugate l a, fun a => ?_, ?_⟩
  · refine (loc B e).mul_mem hvi ?_
    rw [← RingHom.map_adjugate]
    exact (N'.adjugate l a).2
  · have h3 : (ι.mapMatrix N').mulVec t = r := by
      ext a; rw [hmul a]; rfl
    have h4 : ((ι.mapMatrix N').adjugate).mulVec r = (ι.mapMatrix N').det • t := by
      rw [← h3, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h5 := congrFun h4 l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h5
    simp only [mul_assoc]
    rw [← Finset.mul_sum, h5, inv_mul_cancel_left₀ hv0]

theorem UpperTheory.Gal.productCup_of_system.fixLoc_of :
    ValBasic → FixLoc := by
  intro hV F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 Fx A hY e he
  have htan := hY.tan e he
  choose g hgv hgs using htan
  refine fixLoc_key hV (rB ℂ K' (xv x) {0}) e.1 g (A e) (tt K' x) _ hgv (hY.det e he) fun a => ?_
  rw [← hgs a]
  have hd : ofLex (dj (0 : Fin (d + 1)) a) = (a.succ, 0) := by
    show (Fin.succAbove 0 a, (0 : Fin (d + 1))) = _
    rw [Fin.succAbove_zero]
  have hx0 : algebraMap F K' (x 0 : F) ≠ 0 := by simp
  have hy0 : j2 (algebraMap F K (x 0 : F)) ≠ 0 := by simp
  have hmu : (sysY x j2 d).mu (dj 0 a) = algebraMap F K' (x a.succ : F) * j2 (algebraMap F K (x 0 : F))
      - algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x a.succ : F)) := by
    unfold Sys.mu
    rw [hd]
    rfl
  have hu : (((sysY x j2 d).u n11 0 0 (dj 0 a) : K'ˣ) : K') =
      algebraMap F K' (x 0 : F) * j2 (algebraMap F K (x 0 : F)) := by
    unfold Sys.u n11
    simp only [pow_one, Units.val_mul]
    rfl
  unfold Sys.r
  rw [Units.val_inv_eq_inv_val, hu, hmu]
  simp only [tt, map_div₀]
  field_simp
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    lft s ⊆ lft t := by
  intro a ha
  simp only [lft, Finset.mem_toLeft, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma rgt_mono' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {s t : Finset (ι ⊕ₗ κ)} (h : s ⊆ t) :
    rgt s ⊆ rgt t := by
  intro a ha
  simp only [rgt, Finset.mem_toRight, Finset.mem_map] at ha ⊢
  obtain ⟨u, hu, e⟩ := ha
  exact ⟨u, h hu, e⟩

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q := by
  refine Submodule.span_mono ?_
  rintro y ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, h hb, v, fun j => h (hv j), rfl⟩

private lemma wd_empty' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] (w : ι → Module.End ℂ E)
    (c : Finset ι → E) : wd w c ∅ = 0 := by
  simp [wd]

private lemma acx_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {w : ι → Module.End ℂ E} {n : ℤ} {c : Finset ι → E} :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

private lemma cech_C' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] {A : Finset ι → Submodule ℂ E}
    {n : ℤ} {c : Finset ι → E} :
    c ∈ (cech A).C n ↔ ∀ s, c s ∈ (if s.Nonempty ∧ (s.card : ℤ) = n + 1 then A s else ⊥ : Submodule ℂ E) :=
  ⟨fun h s => h s trivial, fun h s _ => h s⟩

theorem UpperTheory.Gal.productCup_of_system.edgeB_of :
    EdgeInj → RowEx → L1 → RYBasic → WdUni → WdBasic → EdgeB := by
  intro hEI hRow hL1 hRY hU hW
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 y hy hB
  obtain ⟨hRI, hGood, hRmono, -, -⟩ := hRY F K K' d x j2 h0
  have lu : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.1
  have ru : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.1
  have cu : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) I J).2.2.2.1
  let G : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) d
  have hGm : ∀ I J, G (uni I J) = omB ℂ K' (RY (xv x) j2 I J) d := by
    intro I J
    simp only [G, lu, ru]
  have hG0 : ∀ I, G (uni I ∅) = omB ℂ K' (rB ℂ K' (xv x) I) d := by
    intro I
    rw [hGm, hRI]
  have hcech : (fun I => G (uni I ∅)) = fun I => omB ℂ K' (rB ℂ K' (xv x) I) d := funext hG0
  have hmix : (fun I J => G (uni I J)) = fun I J => omB ℂ K' (RY (xv x) j2 I J) d :=
    funext fun I => funext fun J => hGm I J
  obtain ⟨γ, hγ, hγ0, hγI⟩ := hEI (Fin (d + 1)) (DR ℂ K') G d y
    (by rw [hcech]; exact hy) (by rw [hmix]; exact hB)
  let A : Finset (Two d) → Submodule ℂ (DR ℂ K') := fun s => if (lft s).Nonempty then G s else ⊥
  have hAn : ∀ s, (lft s).Nonempty → A s = G s := fun s hs => if_pos hs
  have hAe : ∀ s, ¬ (lft s).Nonempty → A s = ⊥ := fun s hs => if_neg hs
  have hWOk : WOk A (fun _ => 1) := by
    refine ⟨fun _ _ => Commute.one_left _, ?_⟩
    intro s i _ m hm
    by_cases hs : (lft s).Nonempty
    · have hsub : s ⊆ insert i s := Finset.subset_insert _ _
      have hs' : (lft (insert i s)).Nonempty := hs.mono (lft_mono' hsub)
      rw [hAn _ hs] at hm
      show m ∈ A (insert i s)
      rw [hAn _ hs']
      exact omB_mono' (hRmono _ _ _ _ (lft_mono' hsub) (rgt_mono' hsub)) d hm
    · rw [hAe _ hs, Submodule.mem_bot] at hm
      show m ∈ A (insert i s)
      rw [hm]
      exact Submodule.zero_mem _
  have hKE : ∀ b, KE (colA A (fun _ => 1) b) ((d : ℤ) + 2) := by
    intro b m _
    by_cases hb : b.Nonempty
    · have e : (fun L => A (uni b L)) = fun J => omB ℂ K' (RY (xv x) j2 b J) d := by
        funext L
        rw [hAn _ (by rw [lu]; exact hb), hGm]
      show (acx (fun L => A (uni b L)) fun _ => 1).Z m ≤ (acx (fun L => A (uni b L)) fun _ => 1).B m
      rw [e]
      exact hRow F K K' d x j2 h0 d b hb m
    · intro c hc
      have hc0 : c = 0 := by
        funext L
        have h1 := acx_C'.1 hc.1 L
        have hA : A (uni b L) = ⊥ := hAe _ (by rw [lu]; exact hb)
        have h2 : c L ∈ (⊥ : Submodule ℂ (DR ℂ K')) := by
          simp only [hA, ite_self] at h1
          exact h1
        exact (Submodule.mem_bot ℂ).1 h2
      rw [hc0]
      exact Submodule.zero_mem _
  have hdelta : ∀ c : Finset (Two d) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Two d) (DR ℂ K') A (fun _ => 1)).2.2.2.2.1
  have hdelta' : ∀ c : Finset (Fin (d + 1)) → DR ℂ K', wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) c = deltaL ℂ _ _ c :=
    (hW (Fin (d + 1)) (DR ℂ K') (fun _ => ⊥) (fun _ => 1)).2.2.2.2.1
  have hγZ : γ ∈ (acx A fun _ => 1).Z ((d : ℤ) + 1) := by
    refine ⟨?_, ?_⟩
    · refine acx_C'.2 fun s => ?_
      have h1 := cech_C'.1 hγ.1 s
      by_cases hc : (s.card : ℤ) = (d : ℤ) + 1
      · rw [if_pos hc]
        by_cases hs : (lft s).Nonempty
        · rw [hAn _ hs]
          have hne : s.Nonempty := by
            rw [← Finset.card_pos]
            omega
          rw [if_pos ⟨hne, hc⟩] at h1
          exact h1
        · rw [hAe _ hs, Submodule.mem_bot]
          have hl : lft s = ∅ := Finset.not_nonempty_iff_eq_empty.1 hs
          have := hγ0 (rgt s)
          rwa [← hl, (hU _ _ (DR ℂ K') (fun _ => 1) (fun _ => 0) ∅ ∅).2.2.2.2 s] at this
      · rw [if_neg hc]
        rw [if_neg (fun h => hc h.2)] at h1
        exact h1
    · show wd _ γ = 0
      rw [hdelta]
      exact hγ.2
  have hBγ : γ ∈ (acx A fun _ => 1).B ((d : ℤ) + 1) := by
    refine hL1 (Fin (d + 1)) (Fin (d + 1)) (DR ℂ K') A (fun _ => 1) ((d : ℤ) + 2) ((d : ℤ) + 1) hWOk hKE γ hγZ ?_ ?_
    · intro b L hL
      exfalso
      have : L.card ≤ d + 1 := by simpa using Finset.card_le_univ L
      omega
    · intro b hb
      exfalso
      have : (0 : ℤ) ≤ b.card := by positivity
      omega
  obtain ⟨η, hη, he⟩ := hBγ
  refine Submodule.mem_map.2 ⟨fun b => η (uni b ∅), ?_, ?_⟩
  · refine cech_C'.2 fun b => ?_
    have h1 := acx_C'.1 hη (uni b ∅)
    rw [cu] at h1
    simp only [Finset.card_empty, add_zero] at h1
    by_cases hb : b.Nonempty ∧ (b.card : ℤ) = (d : ℤ) - 1 + 1
    · rw [if_pos hb]
      have hc : (b.card : ℤ) = (d : ℤ) + 1 - 1 := by omega
      rw [if_pos hc, hAn _ (by rw [lu]; exact hb.1), hG0] at h1
      exact h1
    · rw [if_neg hb]
      by_cases hc : (b.card : ℤ) = (d : ℤ) + 1 - 1
      · have hne : ¬ b.Nonempty := fun h => hb ⟨h, by omega⟩
        rw [if_pos hc, hAe _ (by rw [lu]; exact hne)] at h1
        exact h1
      · rw [if_neg hc] at h1
        exact h1
  · funext I
    have e1 := (hU _ _ (DR ℂ K') (fun _ => 1) η I ∅).1
    rw [wd_empty', smul_zero, add_zero] at e1
    have e2 : wd (fun _ => (1 : Module.End ℂ (DR ℂ K'))) η = γ := he
    rw [e2, hγI] at e1
    rw [e1]
    exact (congrFun (hdelta' _) I).symm
end

section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem locOne_nak {L : Type} [Field L] [Algebra ℂ L] (B O : Subalgebra ℂ L)
    [Algebra.FiniteType ℂ B] (hBO : B ≤ O) (ev : O →ₐ[ℂ] ℂ) (hunit : ∀ u : O, ev u ≠ 0 → IsUnit u)
    (hden : ∀ v : O, ∃ b : B, ev ⟨b, hBO b.2⟩ ≠ 0 ∧ (b : L) * v ∈ B)
    {d : ℕ} (t : Fin d → O) (ht : ∀ l, ev (t l) = 0)
    (hmax : ∀ v : O, ev v = 0 → ∃ a : Fin d → O, v = ∑ l, a l * t l) (v : O) :
    D ℂ L (v : L) ∈ Submodule.span O (Set.range fun l => D ℂ L (t l : L)) := by
  classical
  set I : Ideal O := RingHom.ker ev with hI
  set N : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun l => D ℂ L (t l : L)) with hN
  set M : Submodule O (Ω[L⁄ℂ]) := Submodule.span O (Set.range fun w : O => D ℂ L (w : L)) with hM
  have hvM : D ℂ L (v : L) ∈ M := Submodule.subset_span ⟨v, rfl⟩
  suffices hMN : M ≤ N from hMN hvM
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := I)
  · obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℂ B).out
    set G : Submodule O (Ω[L⁄ℂ]) := Submodule.span O ((fun b : B => D ℂ L (b : L)) '' (s : Set B)) with hG
    have hB : ∀ b : B, D ℂ L (b : L) ∈ G := by
      intro b
      have hb : b ∈ Algebra.adjoin ℂ (s : Set B) := hs ▸ Algebra.mem_top
      induction hb using Algebra.adjoin_induction with
      | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
      | algebraMap r => simp
      | add y z _ _ hy hz =>
        rw [Subalgebra.coe_add, map_add (f := _)]
        exact Submodule.add_mem _ hy hz
      | mul y z _ _ hy hz =>
        rw [Subalgebra.coe_mul, Derivation.leibniz]
        exact Submodule.add_mem _ (Submodule.smul_mem G (⟨y, hBO y.2⟩ : O) hz)
          (Submodule.smul_mem G (⟨z, hBO z.2⟩ : O) hy)
    have hGM : M = G := by
      apply le_antisymm
      · rw [hM, Submodule.span_le]
        rintro _ ⟨w, rfl⟩
        obtain ⟨b, hb0, hbw⟩ := hden w
        obtain ⟨u, hu⟩ := hunit _ hb0
        have h1 : D ℂ L ((b : L) * (w : L)) ∈ G := hB ⟨_, hbw⟩
        rw [Derivation.leibniz] at h1
        have h2 : (⟨b, hBO b.2⟩ : O) • D ℂ L (w : L) ∈ G := by
          have h4 := Submodule.sub_mem G h1 (Submodule.smul_mem G w (hB b))
          convert h4 using 1
          simp [Subalgebra.smul_def]
        have h3 := Submodule.smul_mem G (↑u⁻¹ : O) h2
        rw [← hu, smul_smul, Units.inv_mul, one_smul] at h3
        exact h3
      · rw [hG, Submodule.span_le]
        rintro _ ⟨b, _, rfl⟩
        exact Submodule.subset_span ⟨⟨b, hBO b.2⟩, rfl⟩
    rw [hGM]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · intro y hy
    rw [Ideal.mem_jacobson_bot]
    intro z
    apply hunit
    have hy0 : ev y = 0 := hy
    simp [hy0]
  · rw [hM, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    obtain ⟨a, ha⟩ := hmax (w - algebraMap ℂ O (ev w)) (by simp)
    have hD : D ℂ L (w : L) = ∑ l, ((a l : O) • D ℂ L (t l : L) + (t l : O) • D ℂ L (a l : L)) := by
      have h1 : (w : L) = algebraMap ℂ L (ev w) + ∑ l, (a l : L) * (t l : L) := by
        have h5 := congrArg (fun u : O => (u : L)) ha
        push_cast at h5
        linear_combination h5

      rw [h1, map_add (f := _), Derivation.map_algebraMap, zero_add, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Derivation.leibniz]
      rfl
    show D ℂ L (w : L) ∈ _
    rw [hD]
    refine Submodule.sum_mem _ fun l _ => Submodule.add_mem _ ?_ ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    · apply Submodule.mem_sup_right
      apply Submodule.smul_mem_smul
      · show ev (t l) = 0
        exact ht l
      · exact Submodule.subset_span ⟨a l, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.locOne_of :
    LocMax → ValBasic → LocOne := by
  intro hMax hVal F L _ _ _ _ _ _ d x hc hred e v hv
  obtain ⟨hle, ⟨ev, hev⟩, hbv, hinv⟩ := hVal L (rB ℂ L (xv x) {0}) e.1
  haveI := hc.smooth 0
  haveI : Algebra.FiniteType ℂ (rB ℂ L (xv x) {0}) := inferInstance
  have hevB : ∀ b : rB ℂ L (xv x) {0}, ev ⟨b, hle b.2⟩ = e.1 b := by
    intro b
    obtain ⟨h, hb⟩ := (hev _ _).1 (hbv b)
    exact hb
  have hunit : ∀ u : loc (rB ℂ L (xv x) {0}) e.1, ev u ≠ 0 → IsUnit u := by
    intro u hu
    obtain ⟨h0, h1⟩ := hinv u (ev u) ((hev _ _).2 ⟨u.2, rfl⟩) hu
    exact IsUnit.of_mul_eq_one (⟨_, h1⟩ : loc (rB ℂ L (xv x) {0}) e.1)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hden : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ∃ b : rB ℂ L (xv x) {0},
      ev ⟨b, hle b.2⟩ ≠ 0 ∧ (b : L) * v ∈ rB ℂ L (xv x) {0} := by
    intro v
    obtain ⟨b, hb, hbv'⟩ := v.2
    exact ⟨b, by rw [hevB]; exact hb, hbv'⟩
  let t : Fin d → loc (rB ℂ L (xv x) {0}) e.1 := fun l => ⟨tt L x l, hle (tco_mem ℂ L (xv x) l)⟩
  have ht : ∀ l, ev (t l) = 0 := fun l =>
    (hevB ⟨_, tco_mem ℂ L (xv x) l⟩).trans (e.2 l)
  have hmax : ∀ v : loc (rB ℂ L (xv x) {0}) e.1, ev v = 0 → ∃ a : Fin d → loc (rB ℂ L (xv x) {0}) e.1,
      v = ∑ l, a l * t l := by
    intro v h0
    obtain ⟨a, ha, hv'⟩ := hMax F L d x hc hred e v ((hev _ _).2 ⟨v.2, h0⟩)
    refine ⟨fun l => ⟨a l, ha l⟩, Subtype.ext ?_⟩
    rw [hv', AddSubmonoidClass.coe_finsetSum]
    rfl
  have hmem := locOne_nak _ _ hle ev hunit hden t ht hmax ⟨v, hv⟩
  obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
  exact ⟨fun l => c l, fun l => (c l).2, hc'.symm⟩
end
