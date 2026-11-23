module

public import Formalism.SharpRestriction.GrowthBounds.PathWeight.GeneratorImageIsSymbol
public import Formalism.SharpRestriction.GrowthBounds.PathWeight.FixedSymbolFactorIntegral
public import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
public import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
public import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section XX

variable {O : Type} [CommRing O] [IsDomain O] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ)

theorem xx_mono (mg : ℤ → ℤ) (th o : ℤ → ℝ) (hmg : ∀ x, 0 ≤ mg x) :
    XX' O r K F j mg th o ≤ XX' O r K F j (fun _ => 0) th o := by
  unfold XX'
  apply inf_le_inf_right
  apply Submodule.span_mono
  rintro P ⟨A, G, M, hA, hG, hc, rfl⟩
  refine ⟨A, G, M, hA, hG, fun x hx hW => ?_, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hc x hx hW
  have key : ∀ v : WithTop ℤ, ((M x + mg x : ℤ) : WithTop ℤ) ≤ v → ((M x + 0 : ℤ) : WithTop ℤ) ≤ v :=
    fun v hv => le_trans (WithTop.coe_le_coe.mpr (by linarith [hmg x])) hv
  exact ⟨fun he => ⟨(h1 he).1, key _ (h1 he).2⟩, fun he => ⟨(h2 he).1, key _ (h2 he).2⟩, h3⟩

end XX

section Comp

variable {p n' r k : ℕ} [Fact p.Prime] [NeZero n'] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF p n') O]
  {w : O} {Fr : Frames n' r} {Q : ℕ} {g : Matrix (Fin k) (Fin k) (WF p n')}

local notation "PP" => MvPolynomial (TV n' k) (KK O)

theorem SyS_compZ {H0 : PP} (hH0 : IsWeightedHomogeneous (normalVariableWeight n' k r) H0 0) {Z : PP} (hZ : Z ∈ SyS w Fr Q g) (o : ℕ) :
    ∃ FinalForm ∈ SyS w Fr Q g, weightedHomogeneousComponent (normalVariableWeight n' k r) o (Z * H0) = FinalForm * H0 := by
  induction hZ using AddSubmonoid.closure_induction with
  | mem P hP =>
    obtain ⟨o', hS⟩ := hP
    have hh : IsWeightedHomogeneous (normalVariableWeight n' k r) P o' := (hom_iff P o').mp hS.1
    have hm : IsWeightedHomogeneous (normalVariableWeight n' k r) (P * H0) o' := by simpa using hh.mul hH0
    by_cases he : o = o'
    · subst he
      exact ⟨P, SyS_of_Sy hS, hm.weightedHomogeneousComponent_same⟩
    · exact ⟨0, zero_mem _, by rw [hm.weightedHomogeneousComponent_ne o he, zero_mul]⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨Za, hZa, ea⟩ := ha
    obtain ⟨Zb, hZb, eb⟩ := hb
    exact ⟨Za + Zb, add_mem hZa hZb, by rw [add_mul, map_add (f := _), ea, eb, add_mul]⟩

end Comp

theorem sum_comp_range {R σ : Type*} [CommSemiring R] (wt : σ → ℕ) (φ : MvPolynomial σ R) (T : ℕ)
    (h : ∀ m ∈ φ.support, Finsupp.weight wt m ≤ T) :
    ∑ o ∈ Finset.range (T + 1), weightedHomogeneousComponent wt o φ = φ := by
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with hd
  · rfl
  · symm
    by_contra hne
    exact hd (Finset.mem_range.mpr (Nat.lt_succ_of_le (h d (mem_support_iff.mpr hne))))

theorem normDeg_eq_vsDeg {n' r K : ℕ} (m : Fin n' × Fin (r + K) →₀ ℕ) : normDeg r m = vsDeg m := by
  unfold normDeg vsDeg
  rw [Finset.sum_subset (Finset.subset_univ m.support)
    (fun v _ hv => by simp [Finsupp.notMem_support_iff.mp hv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Fin.sum_univ_add]
  by_cases ht : Even t.val
  · simp only [IsNormal, ht, ite_true]
    simp
  · simp only [IsNormal, ht, ite_false]
    simp

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility MvPolynomial

theorem lamAt_add {n' m : ℕ} (lam mu : Fin n' → Fin (m + 1) → ℤ) (s : Fin n') :
    lamAt (lam + mu) s = lamAt lam s + lamAt mu s := by
  unfold lamAt
  split_ifs
  · rfl
  · funext i
    simp only [Pi.add_apply, neg_add]

theorem Ar_add {n' m : ℕ} (r : ℕ) (lam mu : Fin n' → Fin (m + 1) → ℤ) :
    Ar r (lam + mu) = Ar r lam + Ar r mu := by
  unfold Ar
  simp only [lamAt_add, Pi.add_apply, Finset.sum_add_distrib]

theorem isDominant_add {n' m : ℕ} {lam mu : Fin n' → Fin (m + 1) → ℤ} (h1 : IsDominant lam) (h2 : IsDominant mu) :
    IsDominant (lam + mu) := by
  intro s
  exact (h1 s).add (h2 s)

theorem nuOf_add {m : ℕ} {a b : Fin (m + 1) → ℤ} (ha : Antitone a) (hb : Antitone b) :
    nuOf (a + b) = nuOf a + nuOf b := by
  funext t
  have h1 : 0 ≤ a t - a (Fin.last m) := sub_nonneg.2 (ha (Fin.le_last t))
  have h2 : 0 ≤ b t - b (Fin.last m) := sub_nonneg.2 (hb (Fin.le_last t))
  simp only [nuOf, Pi.add_apply]
  rw [show a t + b t - (a (Fin.last m) + b (Fin.last m)) =
      (a t - a (Fin.last m)) + (b t - b (Fin.last m)) by ring]
  exact Int.toNat_add h1 h2

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ)
    {F G : MvPolynomial (Fin r × Fin n) R} (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') :
    F * G ∈ dualWeyl R r n (ν + ν') := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hF hG ⊢
  refine ⟨hF.1.mul hG.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hF.2 l j hlj, hG.2 l j hlj]

theorem tensorLat_mul (R K : Type*) [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}
    (M M' M'' : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ M' s, F * G ∈ M'' s)
    {x y : MvPolynomial (S × (Fin k × Fin n)) K} (hx : x ∈ tensorLat R K M) (hy : y ∈ tensorLat R K M') :
    x * y ∈ tensorLat R K M'' := by
  have key : tensorLat R K M * tensorLat R K M' ≤ tensorLat R K M'' := by
    unfold tensorLat
    rw [Submodule.span_mul_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
    refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
    simp only [map_mul, Finset.prod_mul_distrib]
  exact key (Submodule.mul_mem_mul hx hy)

theorem V_mul (Kf : Type*) [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu)
    {x y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf} (hx : x ∈ Vsp Kf lam) (hy : y ∈ Vsp Kf mu) :
    x * y ∈ Vsp Kf nu := by
  subst hnu
  unfold Vsp at hx hy ⊢
  refine tensorLat_mul Kf Kf _ _ _ ?_ hx hy
  intro s F hF G hG
  have hs := lamAt_add lam mu s
  by_cases ha : Antitone (lamAt lam s)
  · by_cases hb : Antitone (lamAt mu s)
    · have hab : Antitone (lamAt (lam + mu) s) := by
        rw [hs]
        exact ha.add hb
      rw [if_pos ha] at hF
      rw [if_pos hb] at hG
      rw [if_pos hab, hs, nuOf_add ha hb]
      exact dualWeyl_mul Kf (m + 1) (m + 1) _ _ hF hG
    · rw [if_neg hb, Submodule.mem_bot] at hG
      rw [hG, mul_zero]
      exact Submodule.zero_mem _
  · rw [if_neg ha, Submodule.mem_bot] at hF
    rw [hF, zero_mul]
    exact Submodule.zero_mem _

def mulV {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) : Vsp Kf nu :=
  ⟨(x : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y, V_mul Kf hnu h1 h2 x.2 y.2⟩

@[simp] theorem mulV_coe {Kf : Type*} [Field Kf] {n' m : ℕ} {lam mu nu : Fin n' → Fin (m + 1) → ℤ}
    (hnu : nu = lam + mu) (h1 : IsDominant lam) (h2 : IsDominant mu) (x : Vsp Kf lam) (y : Vsp Kf mu) :
    ((mulV hnu h1 h2 x y : Vsp Kf nu) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y := rfl

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_scale (a b : Kf) (M : Submodule O X) : scale a (scale b M) = scale (a * b) M := by
  unfold scale
  rw [← Submodule.map_comp]
  congr 1
  ext x
  show a • (b • x) = (a * b) • x
  rw [mul_smul]

end Scale

section Lat

variable {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}

theorem toV_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) (α β : Kf)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale α (toV lam (Hten O lam Λ))) (hy : y ∈ scale β (toV mu (Hten O mu Λ))) :
    z ∈ scale (α * β) (toV nu (Hten O nu Λ)) := by
  subst hnu
  obtain ⟨x0, hx0, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨y0, hy0, rfl⟩ := Submodule.mem_map.1 hy
  have hmem : ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0) ∈ Hten O (lam + mu) Λ :=
    hM O Kf n' m lam mu Λ h1 h2 _ (Submodule.mem_comap.1 hx0) _ (Submodule.mem_comap.1 hy0)
  refine Submodule.mem_map.2 ⟨⟨(x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * y0,
    V_mul Kf rfl h1 h2 x0.2 y0.2⟩, hmem, ?_⟩
  apply Subtype.ext
  rw [hz]
  show (α * β) • ((x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
      (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
    (α • (x0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) * (β • (y0 : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
  rw [smul_mul_smul_comm]

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

theorem HL_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (L : Submodule W (Fin (m + 1) → Qq)) (c : Kf) (hc : c ≠ 0) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (c ^ a) (HL (O := O) ι σ lam L)) (hy : y ∈ scale (c ^ b) (HL (O := O) ι σ mu L)) :
    z ∈ scale (c ^ (a + b)) (HL (O := O) ι σ nu L) := by
  rw [zpow_add₀ hc]
  exact toV_mul D hM hnu h1 h2 _ _ _ hz hx hy

theorem Re_mul (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1)) (a b : ℤ)
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ scale (algebraMap O Kf w ^ a) (Re p ι σ w r lam e))
    (hy : y ∈ scale (algebraMap O Kf w ^ b) (Re p ι σ w r mu e)) :
    z ∈ scale (algebraMap O Kf w ^ (a + b)) (Re p ι σ w r nu e) := by
  subst hnu
  unfold Re HLe at hx hy ⊢
  rw [scale_scale] at hx hy ⊢
  have hz' := toV_mul D hM rfl h1 h2 _ _ _ hz hx hy
  convert hz' using 2
  rw [Ar_add, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw, ← zpow_add₀ hw]
  congr 1
  ring

theorem edge_lattice_mul_of_weight_sum (D : Formalism.BasicNotions.D7) (hM : tableLineDegreeFive.LevelPrimesProviso D) (p : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O)
    (hw : algebraMap O Kf w ≠ 0) (r : ℕ)
    {lam mu nu : Fin n' → Fin (m + 1) → ℤ} (hnu : nu = lam + mu)
    (h1 : IsDominant lam) (h2 : IsDominant mu) (e : Edge W Qq (m + 1))
    {x : Vsp Kf lam} {y : Vsp Kf mu} {z : Vsp Kf nu}
    (hz : (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = x * y)
    (hx : x ∈ Re p ι σ w r lam e) (hy : y ∈ Re p ι σ w r mu e) : z ∈ Re p ι σ w r nu e := by
  have h1s : ∀ {lam0 : Fin n' → Fin (m + 1) → ℤ} (M : Submodule O (Vsp Kf lam0)), scale (1 : Kf) M = M := by
    intro lam0 M
    unfold scale
    have hid : (LinearMap.lsmul Kf (Vsp Kf lam0) (1 : Kf)).restrictScalars O = LinearMap.id :=
      LinearMap.ext fun v => by simp
    rw [hid, Submodule.map_id]
  have := Re_mul D hM p ι σ w hw r hnu h1 h2 e 0 0 hz (by rw [zpow_zero, h1s]; exact hx)
    (by rw [zpow_zero, h1s]; exact hy)
  rwa [add_zero, zpow_zero, h1s] at this

end Lat

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def ValLe {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (π : O) (D : ℕ) (x : Kf) : Prop :=
  ∃ a b : O, x = algebraMap O Kf a ∧ a * b = π ^ D

section Loc

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]

def SrcTests (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D : ℕ) (κ : ℝ) (cStar : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) : Prop :=
  ∃ (E : Finset (Edge W Qq (m + 1))) (nE : Edge W Qq (m + 1) → ℕ)
    (F : ∀ e : Edge W Qq (m + 1), Fin (nE e) → Vsp Kf lam0),
    (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = L) ∧
    (∀ e ∈ E, ∀ i, F e i ∈ Nsrc p n' ι σ w r lam0 t e.src) ∧
    (∀ e ∈ E, ∀ i, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      F e i ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re p ι σ w r lam0 e')) ∧
    (∀ e ∈ E, ∀ c : Fin (nE e) → O, (∃ i, IsUnit (c i)) →
      ∃ G ∈ Ntgt p n' ι σ w r lam0 t L,
        ValLe (p : O) D (be p r lam0 (∑ i, c i • F e i) G) ∧
        ∀ e' ∈ E, e' ≠ e → G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
    (1 - κ) * (dimV Kf lam0 : ℝ) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ)

def EdgeFam (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (tS tT D cStar : ℕ) (e : Edge W Qq (m + 1)) (n : ℕ) : Prop :=
  ∃ F : Fin n → Vsp Kf lam0,
    (∀ i, F i ∈ scale (algebraMap O Kf w ^ (-(tS : ℤ))) (HL (O := O) ι σ lam0 e.src) ∧ F i ∈ Re p ι σ w r lam0 e) ∧
    (∀ i, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      F i ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re p ι σ w r lam0 e')) ∧
    ∀ c : Fin n → O, (∃ i, IsUnit (c i)) →
      ∃ G : Module.Dual Kf (Vsp Kf lam0),
        G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
        G ∈ Re' p ι σ w r lam0 e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
        ValLe (p : O) D (be p r lam0 (∑ i, c i • F i) G)

end Loc

def Hyps (C : ℝ) (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ) : Prop :=
  13 ≤ p ∧ 2 ≤ r ∧
    tableLineDegreeFive.OrbitHyp n' TT r L₁ L₂ de h x ∧
    orbitWindowCount r de h x ^ 2 ≤ r * TT.card ∧
    tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0 ∧
    (r : ℝ) ≤ Y ∧
    tableLineDegreeFive.La C (orbitWindowCount r de h x) a ≤ ((m + 1 : ℕ) : ℝ) ∧
    orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r ∧
    256 * ((m + 1 : ℕ) : ℝ) ^ 2 * (TT.card : ℝ) * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1) ∧
    C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp ∧
    8 * (Dp + 1) ≤ cStar ∧
    C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) * Y ≤ a

def t0 (C Ct0 : ℝ) (p N N₁ L₁ G' k : ℕ) (a : ℝ) : ℝ :=
  Ct0 * N * (tableLineDegreeFive.La C N₁ a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G')

def om (r N n' c0 cpp : ℕ) : ℝ := (r : ℝ) * N * c0 + 2 * r * n' * cpp

def EdgeStep (C Ct0 CD1 Cr : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
      ∃ n tS tT D1 : ℕ,
        (tS : ℝ) ≤ t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + om r TT.card n' c0 cpp ∧
        (tT : ℝ) ≤ t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp ∧
        (D1 : ℝ) ≤ CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
        (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) *
            (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (dimV Kf lam0 : ℝ) / ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) ≤ n ∧
        EdgeFam (W := W) (O := O) p n' ι σ w r lam0 tS tT D1 cStar e n

def RestEdge (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 Cr C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < Cr ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0 CD1 Cr

def ManyEdges : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (k r : ℕ), r ≤ k →
      ∃ E : Finset (Edge W Qq k),
        (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = colSpan W (1 : Matrix (Fin k) (Fin k) Qq)) ∧
        p ^ (n' * (r * (k - r))) ≤ E.card

def S7 : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w → BePerfect →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
      (L : Submodule W (Fin (m + 1) → Qq)), IsDominant lam0 → 2 * (D + 1) ≤ cStar →
      SrcTests (O := O) p n' ι σ w r lam0 t D κ cStar L → LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L

def Asm : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
      (L : Submodule W (Fin (m + 1) → Qq)) (E : Finset (Edge W Qq (m + 1))) (nE : Edge W Qq (m + 1) → ℕ),
      (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = L) →
      (∀ e ∈ E, ∃ tS tT D1 : ℕ, tS ≤ t ∧ tT ≤ t ∧ D1 ≤ D ∧
        EdgeFam (W := W) (O := O) p n' ι σ w r lam0 tS tT D1 cStar e (nE e)) →
      (1 - κ) * (dimV Kf lam0 : ℝ) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ) →
      SrcTests (O := O) p n' ι σ w r lam0 t D κ cStar L

def Num : Prop :=
  ∀ (C Ct0 CD1 Cr : ℝ), 0 < Ct0 → 0 < CD1 → 0 < Cr → 2 ≤ C → Ct0 ≤ C → CD1 ≤ C → Cr + 1 ≤ C →
    ∀ (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
      (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
      Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
      t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp ≤
        tableLineDegreeFive.tBound C p r TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) n' (m + 1) cpp c0 a ∧
      0 ≤ (TT.card : ℝ) * c0 ∧
      CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp ∧
      1 - C * TT.card * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y ≤
        (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) * (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card

end Formalism.MainNotions.Pf14
end
end
