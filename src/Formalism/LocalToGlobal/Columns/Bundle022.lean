module

public import Formalism.LocalToGlobal.Columns.ChainOneB
public import Formalism.LocalToGlobal.Columns.Bundle014
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral
public import Formalism.LocalToGlobal.Columns.CmUnramifiedOfFieldConditions
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.LocalRingCardinality.Bundle009
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.Bundle008
import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.Columns.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ocbT_bEnt_comp (hq0 : (q : E) ≠ 0) {n' c' n c : ℕ} (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c))
    {l s : ℕ} (hl : l < n + c) (hs : s < n' + c') :
    ocbBEnt n' n q (g ∘ₗ y) l s = ∑ m : Fin (n + c), ocbBEnt n n q g l m.1 * ocbBEnt n' n q y m.1 s := by
  unfold ocbBEnt
  rw [ocbS_atN_comp g y hl hs, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hz : ((q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) =
      (q : E) ^ (LocE.scE n (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) *
        (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) m.1) := by
    rw [← zpow_add₀ hq0]
    congr 1
    ring
  rw [hz]
  ring

private theorem intAt_apply_of_mem_stdAt {N : ℕ} {x : Sp E N} (hx : x ∈ stdAt E N P) (i : Fin N) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  rw [mem_stdLat] at hsx
  obtain ⟨r, hr⟩ := hsx i
  exact ⟨r, s, hs, by rw [hr]; simp [Algebra.smul_def]⟩

private theorem mem_sclLat_iff_scaled_mem_stdAt {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ (fun l : Fin N => ((q : E) ^ e l)⁻¹ * x l) ∈ stdAt E N P := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap]
  rfl

theorem ocbT_int_of_stab (hq0 : (q : E) ≠ 0) {n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) {l m : ℕ} (hl : l < n + c) (hm : m < n + c) :
    IntAt P (ocbBEnt n n q g.toLinearMap l m) := by
  set e := LocE.scE n (fun i => i + 1) with he
  let v : Sp E (n + c) := fun i => if (i : ℕ) = m then (q : E) ^ (e m) else 0
  have hv : v ∈ LocE.lamY P q n c (fun i => i + 1) := by
    unfold LocE.lamY
    rw [mem_sclLat_iff_scaled_mem_stdAt]
    refine ⟨1, one_mem _, ?_⟩
    rw [one_smul, mem_stdLat]
    intro i
    by_cases hi : (i : ℕ) = m
    · refine ⟨1, ?_⟩
      simp only [v, hi, if_true, map_one]
      rw [← he, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
    · exact ⟨0, by simp [v, hi]⟩
  have hg' : ∀ x, g x ∈ LocE.lamY P q n c (fun i => i + 1) ↔ x ∈ LocE.lamY P q n c (fun i => i + 1) := hg
  have hgv := (hg' v).2 hv
  unfold LocE.lamY at hgv
  rw [mem_sclLat_iff_scaled_mem_stdAt] at hgv
  have hint := intAt_apply_of_mem_stdAt hgv ⟨l, hl⟩
  have hv' : v = ((q : E) ^ (e m)) • Loc.eN E (n + c) m := by
    funext i
    by_cases hi : (i : ℕ) = m <;> simp [v, Loc.eN, hi]
  convert hint using 1
  unfold ocbBEnt
  rw [ocbS_atN_of_lt _ hl]
  simp only [LinearEquiv.coe_coe, hv', map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← he, zpow_sub₀ hq0]
  ring

theorem ocbT_bEnt_id {n c l s : ℕ} (hl : l < n + c) :
    ocbBEnt n n q (LinearMap.id : Sp E (n + c) →ₗ[E] Sp E (n + c)) l s = if l = s then 1 else 0 := by
  unfold ocbBEnt
  rw [LinearMap.id_apply, ocbS_atN_of_lt _ hl]
  by_cases h : l = s
  · subst h
    simp [Loc.eN]
  · simp [Loc.eN, h]

theorem ocbT_red_symm (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    Loc.atN (hbar.symm (Loc.eN _ (n + c) s)) l = redP P (ocbBEnt n n q h₀.symm.toLinearMap l s) := by
  classical
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hI1 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hh₀ hi hm
  have hI2 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.symm.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hsymm hi hm
  have hDA : LinearMap.toMatrix' hbar.symm.toLinearMap * LinearMap.toMatrix' hbar.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hAC : LinearMap.toMatrix' hbar.toLinearMap *
      (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hcomp := ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap i.2 j.2
    rw [LinearEquiv.comp_symm, ocbT_bEnt_id i.2] at hcomp
    have hsum : ∑ m : Fin (n + c), LinearMap.toMatrix' hbar.toLinearMap i m *
        (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) m j =
        redP P (∑ m : Fin (n + c),
          ocbBEnt n n q h₀.toLinearMap i m * ocbBEnt n n q h₀.symm.toLinearMap m j) := by
      rw [redP_sum _ _ (fun m _ => IntAt.mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2))]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [reduction_mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2), Matrix.of_apply, ocbS_atN_toMatrix']
      congr 1
      exact (hred₀ _ _ i.2 m.2).2
    rw [hsum, ← hcomp, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [redP_one]
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij', redP_zero]
  have hCD : (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) =
      LinearMap.toMatrix' hbar.symm.toLinearMap := by
    rw [← Matrix.one_mul (Matrix.of _), ← hDA, Matrix.mul_assoc, hAC, Matrix.mul_one]
  have h1 := congrFun (congrFun hCD ⟨l, hl⟩) ⟨s, hs⟩
  rw [Matrix.of_apply, ocbS_atN_toMatrix'] at h1
  exact h1.symm

theorem ocbT_trans (hq0 : (q : E) ≠ 0) {K L : Type} [Field K] [Field L] (σ : K →+* L) {n' c' c'' n c : ℕ} (hcc : c' = c'')
    {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) (Φ : Loc.SF E K (n' + c') (n + c)) (Φr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + c'') (n + c))
    (hsupp : ∀ y, Φ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Φ y) = Φr ybar) :
    (∀ y, Φ (h₀.symm.toLinearMap ∘ₗ y) ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) ∧
    (∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) →
        σ (Φ (h₀.symm.toLinearMap ∘ₗ y)) = Φr (hbar.symm.toLinearMap ∘ₗ ybar)) := by
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hcomp_int : ∀ (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)),
      (∀ l m, l < n + c → m < n + c → IntAt P (ocbBEnt n n q g l m)) →
      (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q (g ∘ₗ y) l s) := by
    intro g y hg hy l s hl hs
    rw [ocbT_bEnt_comp hq0 g y hl hs]
    exact ciIntAt_sum _ _ (fun m _ => IntAt.mul (hg _ _ hl m.2) (hy _ _ m.2 hs))
  refine ⟨fun y hy => ?_, fun y ybar hy hyb => ?_⟩
  · have h1 := hsupp _ hy
    have h2 := hcomp_int h₀.toLinearMap _ (fun l m hl hm => ocbT_int_of_stab hq0 hh₀ hl hm) h1
    have he : h₀.toLinearMap ∘ₗ (h₀.symm.toLinearMap ∘ₗ y) = y := by
      rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
    rwa [he] at h2
  · have hI := hcomp_int h₀.symm.toLinearMap y (fun l m hl hm => ocbT_int_of_stab hq0 hsymm hl hm) hy
    apply hred _ _ hI
    intro l s hl hs
    have hs' : s < n' + c'' := by omega
    rw [ocbS_atN_comp _ _ hl hs', ocbT_bEnt_comp hq0 _ _ hl hs,
      redP_sum _ _ (fun m _ => IntAt.mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [reduction_mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs), hyb _ _ m.2 hs]
    congr 1
    exact ocbT_red_symm hq0 hh₀ hred₀ hl m.2

end Tr

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.HermitianLatticesTheory

noncomputable section

namespace Formalism.L2.Col

section One

variable (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ)

def autLcm : ℕ := sInf {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D}

variable {E n}

theorem autLcm_mem {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) :
    0 < autLcm E n ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ autLcm E n := by
  have hne : ({D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} : Set ℕ).Nonempty := ⟨D, hD, h⟩
  exact Nat.sInf_mem hne

theorem autLcm_dvd {D : ℕ} (hD : 0 < D) (h : ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D) : autLcm E n ∣ D := by
  obtain ⟨hpos, hdvd⟩ := autLcm_mem hD h
  have hg : 0 < Nat.gcd (autLcm E n) D := Nat.gcd_pos_of_pos_left _ hpos
  have hmem : Nat.gcd (autLcm E n) D ∈ {D : ℕ | 0 < D ∧ ∀ N : UniLat E n, Nat.card (autU E n N) ∣ D} :=
    ⟨hg, fun N => Nat.dvd_gcd (hdvd N) (h N)⟩
  have hle : autLcm E n ≤ Nat.gcd (autLcm E n) D := Nat.sInf_le hmem
  have hge : Nat.gcd (autLcm E n) D ≤ autLcm E n := Nat.le_of_dvd hpos (Nat.gcd_dvd_left _ _)
  have heq : Nat.gcd (autLcm E n) D = autLcm E n := le_antisymm hge hle
  rw [← heq]
  exact Nat.gcd_dvd_right _ _

theorem card_autU_dvd_minkM (hE : PosStar E) (N : UniLat E n) :
    Nat.card (autU E n N) ∣ minkM (Module.finrank ℚ E * n) := by
  let φ : autU E n N →* GL (Fin n) E := (ufGL E n).comp (autU E n N).subtype
  have hφ : Function.Injective φ := fun a b hab =>
    Subtype.ext (Subtype.ext ((toGLm E n).injective hab))
  have hfin : Finite (autU E n N) := finite_autU hE N
  have hfin' : Finite φ.range := Finite.of_equiv _ (MonoidHom.ofInjective hφ).toEquiv
  have hst : φ.range ≤ Formalism.UG.stabGL N.1 := by
    rintro _ ⟨a, rfl⟩ x
    have ha : gmap (a.1 : UF E n).1 N.1 = N.1 := congrArg Subtype.val a.2
    show x ∈ _ ↔ ((toGLm E n (a.1 : UF E n).1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).mulVec x ∈ _
    rw [toGLm_mulVec]
    constructor
    · intro hx
      rw [← ha]
      exact Submodule.mem_map_of_mem hx
    · intro hx
      rw [← ha] at hx
      obtain ⟨y, hy, e⟩ := hx
      have : y = x := (a.1 : UF E n).1.injective e
      rwa [← this]
  have h1 := mk_card_dvd minkowskiBound_holds N.1 (hcnt_isFullLattice_of_unimodular N.2.1 N.2.2) φ.range hfin' hst
  rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv] at h1
  exact h1

theorem autLcm_pos (hE : PosStar E) : 0 < autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).1

theorem card_autU_dvd_autLcm (hE : PosStar E) (N : UniLat E n) : Nat.card (autU E n N) ∣ autLcm E n := (autLcm_mem (minkM_pos _) (card_autU_dvd_minkM hE)).2 N

def UniLat.til (N : UniLat E n) : UniLat E (n + 1) := ⟨tilN N.1, tilN_lattice N.2.1, tilN_unimodular N.2.2⟩

def autU_til (N : UniLat E n) : autU E n N →* autU E (n + 1) N.til :=
  (extU.comp (autU E n N).subtype).codRestrict _ fun a => by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    show gmap (extE (a.1 : UF E n).1) (tilN N.1) = tilN N.1
    rw [← tilN_gmap]
    exact congrArg tilN (congrArg Subtype.val a.2)

theorem autU_til_injective (N : UniLat E n) : Function.Injective (autU_til N) := by
  intro a b hab
  have h1 : extE (a.1 : UF E n).1 = extE (b.1 : UF E n).1 :=
    congrArg (fun u : autU E (n + 1) N.til => (u.1 : UF E (n + 1)).1) hab
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, hy⟩ : ∃ y : Sp E (n + 1), initL E n y = x := by
    refine ⟨Fin.snoc (α := fun _ => E) x 0, ?_⟩
    change (fun i : Fin n => (Fin.snoc (α := fun _ => E) x 0 : Fin (n + 1) → E) (Fin.castSucc i)) = x
    funext i
    simp
  subst hy
  calc (a.1 : UF E n).1 (initL E n y) = initL E n (extE (a.1 : UF E n).1 y) := (initL_extE _ _).symm
    _ = initL E n (extE (b.1 : UF E n).1 y) := by rw [h1]
    _ = (b.1 : UF E n).1 (initL E n y) := initL_extE _ _

theorem autLcm_dvd_succ (hE : PosStar E) : autLcm E n ∣ autLcm E (n + 1) := autLcm_dvd (autLcm_pos (E := E) (n := n + 1) hE) fun N =>
    (Subgroup.card_dvd_of_injective (autU_til N) (autU_til_injective N)).trans (card_autU_dvd_autLcm hE N.til)

theorem autLcm_mono (hE : PosStar E) {n n' : ℕ} (h : n ≤ n') : autLcm E n ∣ autLcm E n' := by
  induction h with
  | refl => exact dvd_rfl
  | step _ ih => exact ih.trans (autLcm_dvd_succ hE)

end One

section DGam

def dGamRanks (R : Ranks) : Finset ℕ :=
  (Finset.Icc 1 R.m).image R.N ∪ {R.rankX', R.rankY (R.m - 1), R.nV}

def dGamAut (X : Fields) (R : Ranks) : ℕ := (dGamRanks R).lcm fun n => autLcm X.E n

variable {X : Fields} {R : Ranks}

theorem dga_N_mono (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  simp only [Ranks.N]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem dGamRanks_le (R : Ranks) {n : ℕ} (hn : n ∈ dGamRanks R) : n ≤ R.N R.m := by
  have hm := R.two_le_m
  have hX : R.rankX' ≤ R.N R.m := by
    simp only [Ranks.rankX', Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hY : R.rankY (R.m - 1) ≤ R.N R.m := by
    have h1 : (R.m - 1) * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    simp only [Ranks.rankY, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  have hV : R.nV ≤ R.N R.m := by
    have h2 : 1 * R.t ≤ R.m * R.t := Nat.mul_le_mul_right _ (by omega)
    simp only [Ranks.nV, Ranks.r, Ranks.N, Nat.mul_succ]
    omega
  unfold dGamRanks at hn
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton] at hn
  rcases hn with ⟨j, ⟨_, hj⟩, rfl⟩ | rfl | rfl | rfl
  · exact dga_N_mono R hj
  · exact hX
  · exact hY
  · exact hV

theorem N_m_mem_dGamRanks (R : Ranks) : R.N R.m ∈ dGamRanks R := by
  have hm := R.two_le_m
  unfold dGamRanks
  apply Finset.mem_union_left
  exact Finset.mem_image.2 ⟨R.m, Finset.mem_Icc.2 ⟨by omega, le_rfl⟩, rfl⟩

theorem dGamAut_eq (hX : X.Ok) : dGamAut X R = autLcm X.E (R.N R.m) := by
  have hE := posStar_of_ok hX
  apply Nat.dvd_antisymm
  · exact Finset.lcm_dvd fun n hn => autLcm_mono hE (dGamRanks_le R hn)
  · exact Finset.dvd_lcm (N_m_mem_dGamRanks R)

theorem dGamAut_pos (hX : X.Ok) : 0 < dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_pos (posStar_of_ok hX)

theorem autLcm_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) : autLcm X.E n ∣ dGamAut X R := by
  rw [dGamAut_eq hX]
  exact autLcm_mono (posStar_of_ok hX) hn

theorem card_autU_dvd_dGamAut (hX : X.Ok) {n : ℕ} (hn : n ≤ R.N R.m) (N : UniLat X.E n) :
    Nat.card (autU X.E n N) ∣ dGamAut X R := (card_autU_dvd_autLcm (posStar_of_ok hX) N).trans (autLcm_dvd_dGamAut hX hn)

end DGam

section Stab

variable {X : Fields} {R : Ranks} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem formGSD_stab_dvd_autU (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG) (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) :
    Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ Nat.card (autU X.E n d.lat) := by
  let φ : MulAction.stabilizer (formGSD C Λ).G d →* autU X.E n d.lat :=
    ((MonoidHom.fst (UF X.E n) ↥Λ.grp).comp (MulAction.stabilizer (formGSD C Λ).G d).subtype).codRestrict _ fun a => by
      rw [MulAction.mem_stabilizer_iff]
      exact congrArg DecoSet.lat a.2
  refine Subgroup.card_dvd_of_injective φ fun a b hab => ?_
  have h1 : (a.1.1 : UF X.E n) = b.1.1 := congrArg Subtype.val hab
  exact Subtype.ext (formGSD_stab_inj C Λ d a.2 b.2 h1)

theorem formGSD_stab_dvd_dGamAut (hX : X.Ok) (hn : n ≤ R.N R.m) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ : LevFam X.E X.K n SG)
    (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) : Nat.card (MulAction.stabilizer (formGSD C Λ).G d) ∣ dGamAut X R := (formGSD_stab_dvd_autU C Λ d).trans (card_autU_dvd_dGamAut hX hn _)

theorem dga_frm_stab_inj (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (p : DecoF X.E n ST SG Q) {a b : FrmG Λ Θ}
    (ha : a • p = p) (hb : b • p = p) (hab : a.1 = b.1) : a = b := by
  have hda : ((a.1, (a.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) ha
  have hdb : ((b.1, (b.2.1 : GLG (E := X.E) (n := n) (SG := SG))) • p.deco : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG)) = p.deco :=
    congrArg (fun q : DecoF X.E n ST SG Q => q.1.1) hb
  have h1 := DecoSet.stab_fst_injective p.deco hda hdb hab
  have h2 : (a.2.1 : GLG (E := X.E) (n := n) (SG := SG)) = b.2.1 := congrArg Prod.snd h1
  have h3 : ∀ P : Q, (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 := by
    intro P
    have ea : a.1.1 * p.fr P * (((a.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) ha
    have eb : b.1.1 * p.fr P * (((b.2.2 : GLQ X.E n Q) P)⁻¹).1 = p.fr P :=
      congrArg (fun q : DecoF X.E n ST SG Q => q.1.2 P) hb
    rw [← hab] at eb
    exact mul_left_cancel (ea.trans eb.symm)
  refine Prod.ext hab (Prod.ext (Subtype.ext h2) (Subtype.ext (funext fun P => ?_)))
  exact inv_injective (Subtype.ext (h3 P))

end Stab

end Formalism.L2.Col
end
end
