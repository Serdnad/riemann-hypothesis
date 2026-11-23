module

public import Formalism.LocalToGlobal.Columns.Bundle039
import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.Bundle021
public import Formalism.LocalToGlobal.Columns.RowFormsAdelic
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.HermitianForms.Bundle007
public import Formalism.LocalToGlobal.Columns.ChainTwOk
public import Formalism.LocalToGlobal.Columns.Bundle038
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def tfaExt {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact extE f

theorem tfa_std_iff {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (x : Sp E (n + 1)) :
    x ∈ stdAt E (n + 1) Q ↔ initL E n x ∈ stdAt E n Q ∧ IntAt Q (x (Fin.last n)) := by
  rw [ciMem_stdAt, ciMem_stdAt]
  constructor
  · intro h
    exact ⟨fun i => h _, h _⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases h2 (fun j => ?_) i
    exact h1 j

def tfaD {n : ℕ} (z : E) (hz : z ≠ 0) : Sp E (n + 1) ≃ₗ[E] Sp E (n + 1) :=
  LinearEquiv.piCongrRight fun i : Fin (n + 1) => if i = Fin.last n then LinearEquiv.smulOfNeZero E E z hz else LinearEquiv.refl E E

theorem tfaD_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    tfaD z hz x i = if i = Fin.last n then z * x i else x i := by
  unfold tfaD
  rw [LinearEquiv.piCongrRight_apply]
  split_ifs with h
  · simp [LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  · rfl

theorem tfaD_symm_apply {n : ℕ} (z : E) (hz : z ≠ 0) (x : Sp E (n + 1)) (i : Fin (n + 1)) :
    (tfaD z hz).symm x i = if i = Fin.last n then z⁻¹ * x i else x i := by
  have key : tfaD z hz (fun j => if j = Fin.last n then z⁻¹ * x j else x j) = x := by
    funext j
    rw [tfaD_apply]
    by_cases h : j = Fin.last n
    · subst h
      simp [hz]
    · simp only [h, if_false]
  conv_lhs => rw [← key]
  rw [LinearEquiv.symm_apply_apply]

def tfaExtZ {N n : ℕ} (hN : N = n + 1) (f : Sp E n ≃ₗ[E] Sp E n) (z : E) (hz : z ≠ 0) : Sp E N ≃ₗ[E] Sp E N := by
  subst hN
  exact (tfaD z hz).trans (extE f)

theorem tfaZ_spec {SG : Finset (HeightOneSpectrum (𝓞 E))} {ST : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ} (hN : N = n + 1) (pi : 𝓞 E)
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) (hOk : (d.1.til (ST := ST) pi).Ok) (w : SG) (hw : pi ∉ w.1.asIdeal) (hz : (algebraMap (𝓞 E) E pi) ≠ 0)
    (x : Sp E N) :
    tfaExtZ hN (d.1.liftFr w) (algebraMap (𝓞 E) E pi) hz x ∈ localization₂ w.1.asIdeal (DecoSet.tilH (ST := ST) hN pi d).1.N ↔
      x ∈ stdAt E N w.1 := by
  subst hN
  have hl := Deco.liftFr_spec (d.2.hasLift w)
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (DecoSet.til (ST := ST) pi d).1.N ↔ _
  unfold DecoSet.til
  rw [dif_pos hOk]
  show extE (d.1.liftFr w) (tfaD (algebraMap (𝓞 E) E pi) hz x) ∈ localization₂ w.1.asIdeal (tilN d.1.N) ↔ _
  have hinit : initL E n (tfaD (algebraMap (𝓞 E) E pi) hz x) = initL E n x := by
    funext i
    show tfaD _ hz x (Fin.castSucc i) = x (Fin.castSucc i)
    rw [tfaD_apply, if_neg (Fin.castSucc_ne_last i)]
  have hlast : tfaD (algebraMap (𝓞 E) E pi) hz x (Fin.last n) = algebraMap (𝓞 E) E pi * x (Fin.last n) := by
    rw [tfaD_apply, if_pos rfl]
  rw [mem_localization_tilN, initL_extE, extE_last, hinit, hlast, tfa_std_iff]
  refine and_congr (hl.1 _) ⟨fun h => ?_, fun h => (IntAt.coe w.1 pi).mul h⟩
  have h2 := (xtIntAt_piInv hw).mul h
  rwa [← mul_assoc, inv_mul_cancel₀ hz, one_mul] at h2

end Gen

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (u : Pr.Word)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')


variable (sel mu) in
open Classical in
def topFrA (hQS : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∈ SG') : TopFr (R := R) sel mu u hSG where
  fr P d := if h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal then
      tfaExtZ (N_m_succ R) (d.1.liftFr ⟨P.1, hQS P.1 P.2⟩) (algebraMap (𝓞 X.E) X.E (Pr.piT u))
        (fun h0 => h.2 (by rw [map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 X.E) X.E)] at h0; rw [h0]; exact zero_mem _))
    else frameOfY u P.1 (tilR hSG u d)
  spec P d x := by
    by_cases h : (d.1.til (ST := Pr.vT u) (Pr.piT u)).Ok ∧ Pr.piT u ∉ P.1.asIdeal
    · rw [dif_pos h]
      exact tfaZ_spec (N_m_succ R) (Pr.piT u) d h.1 ⟨P.1, hQS P.1 P.2⟩ h.2 _ x
    · rw [dite_eq_right h]
      exact frameOfY_spec u P.1 (tilR hSG u d) x


end Top

end Formalism.L2.Col.Sc.Fr
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section GenP

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (σ₀ : X.K →+* ℂ) {n : ℕ} [NeZero n]
  (Λ : LevFam X.E X.K n Pr.vGs)

theorem xp_basePi_one : BasePi (∅ : Finset (Pl X.E)) (1 : 𝓞 X.E) :=
  ⟨fun r => ⟨fun _ => one_dvd r, fun _ P hP => absurd hP (Finset.notMem_empty P)⟩,
    isCoprime_one_left⟩

theorem xp_L_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (Pl E)}
    (d : Deco E n (∅ : Finset (Pl E)) SG) : d.L = d.N := by
  unfold Deco.L
  have : {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (Pl E)), d.f P x = 0} = (d.N : Set (Sp E n)) := by
    ext x
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun P => absurd P.2 (Finset.notMem_empty P.1)⟩
  rw [this, Submodule.span_eq]

def tieLevP : Formalism.L2.Forms.StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) xp_basePi_one (by rw [map_one, mul_one, Nat.cast_one])
    (fun P => ⟨fun h => absurd h (Finset.notMem_empty P), fun h => absurd h (one_notMem P)⟩)
    (fun P hP => absurd hP (Finset.notMem_empty P))
    (fun v h => absurd (by rwa [Nat.cast_one] at h) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top))
    (by rw [baseLb_index hc n ∅ (fun P => absurd P.2 (Finset.notMem_empty P.1))]; simp)
    ((Units.map σ₀.toMonoidHom).comp Λ.chr)

variable (s : DecoCl n (∅ : Finset (Pl X.E)) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := ∅) (SG := Pr.vGs))

def clsPG₁ (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c) :
    ClsG hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.N) where
  lev := tieLevP hc σ₀ Λ
  y := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y
  y_bij := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_bij
  y_lat := fun c x => by
    have h := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).y_lat c x
    rw [xp_L_eq_N] at h
    exact h
  stabI := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI
  stabI_inj := (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_inj
  stabI_range := fun c γ => (recCls hc n ∅ Pr.vGs Λ.grp hS 1 s hs).stabI_range c γ.1 γ.2

def clsPG (hS : DecoPtSurj hc n (∅ : Finset (Pl X.E)) Pr.vGs) (hs : ∀ c, decoCls n ∅ Pr.vGs Λ.grp (s c) = c)
    (Q : StepCrd Pr σ₀ n fun c => (s c).1.N) :
    ClsG hc.sig Q.J 1 Q.f Q.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) Q.lat := by
  obtain ⟨J, f, bad, emb, lat, l0, rfl, rfl, rfl, rfl, rfl, rfl⟩ := Q
  exact clsPG₁ hc σ₀ Λ s hS hs

end GenP

section Rec

variable {d : ColDat}

abbrev PCl (d : ColDat) : Type := (ptGSD (Pr := d.Pr) d.W d.levP).Cl

def ColDat.reprP (d : ColDat) (c : PCl d) : DecoSet (E := d.X.E) (n := d.R.N d.R.m - 1) (ST := ∅) (SG := d.Pr.vGs) :=
  (ptGSD (Pr := d.Pr) d.W d.levP).outSec.rep c

def crdPr (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) :
    StepCrd d.Pr d.σ₀ (d.R.N d.R.m - 1) fun c : PCl d => (d.reprP c).1.N where
  J := CF.gramP (d.colRec a)
  f := d.R.f
  bad := CF.badG (d.colRec a)
  emb := CF.embT (d.colRec a)
  lat := fun c => (d.reprP c).1.N
  l0 := stdLat d.X.E (d.R.N d.R.m - 1)
  hJ := gramP_eq a hS
  hf := d.f_eq.symm
  hbad := badG_eq a
  hemb := embT_eq a hH
  hlat := rfl
  hl0 := rfl

def PtSurjP (d : ColDat) : Prop := DecoPtSurj d.sp.cm (d.R.N d.R.m - 1) (∅ : Finset (Pl d.X.E)) d.Pr.vGs

def pClsG (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) :=
  clsPG d.sp.cm d.σ₀ d.levP.inv d.reprP hP (fun c => (ptGSD (Pr := d.Pr) d.W d.levP).outSec.spec c) (crdPr a hS hH)

def parabolicClassAgreement (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d)
    (hP : PtSurjP d) (u : d.what₂.Word) :
    CF.ClsPTied (D := d.colRec a) u where
  lev := (pClsG a hS hH hP).lev
  y := (pClsG a hS hH hP).y
  y_bij := (pClsG a hS hH hP).y_bij
  lat := fun c => (d.reprP c).1.N
  y_lat := (pClsG a hS hH hP).y_lat
  lat_fin := fun c => Module.Finite.iff_fg.2 (d.reprP c).2.lat.fg
  stabI := (pClsG a hS hH hP).stabI
  stabI_inj := (pClsG a hS hH hP).stabI_inj
  stabI_range := (pClsG a hS hH hP).stabI_range

end Rec

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))


include hc hPr in
theorem th_plUnder_vGs (v : HeightOneSpectrum (𝓞 X.F)) :
    v ∈ plUnder X.F Pr.vGs ↔ ((Pr.g 0 : 𝓞 X.F) ∈ v.asIdeal ∨ (Pr.g 1 : 𝓞 X.F) ∈ v.asIdeal) := by
  classical
  have key : ∀ (i : Fin 2), v ∈ plUnder X.F (Pr.vG i) ↔ (Pr.g i : 𝓞 X.F) ∈ v.asIdeal := by
    intro i
    have h0 : X.conjO (Pr.piG i) ≠ 0 := by
      intro h
      have h1 := hPr.piG_norm i
      rw [h, mul_zero] at h1
      exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
    refine mem_plUnder_iff_norm hc (fun P => mem_divs h0 P) (Pr.g i) ?_ v
    have h2 : cO X.E (X.conjO (Pr.piG i)) = Pr.piG i := cO_cO _
    rw [h2, mul_comm]
    exact hPr.piG_norm i
  rw [← key 0, ← key 1]
  constructor
  · rintro ⟨P, hP, h⟩
    rcases Finset.mem_union.1 hP with h' | h'
    · exact Or.inl ⟨P, h', h⟩
    · exact Or.inr ⟨P, h', h⟩
  · rintro (⟨P, hP, h⟩ | ⟨P, hP, h⟩)
    · exact ⟨P, Finset.mem_union_left _ hP, h⟩
    · exact ⟨P, Finset.mem_union_right _ hP, h⟩

variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

def levPack₁ (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) :
    LevPack hc n (1 : Matrix (Fin n) (Fin n) X.E) Pr.g (Pr.T u) X.f (plUnder X.F Pr.vGs)
      (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) (fun c => (s c).1.L) where
  lev := tieLev hc hX hPr σ₀ u Λ
  cls := recCls hc n (Pr.vT u) Pr.vGs Λ.grp hS c₀ s hs
  bad_iff := th_plUnder_vGs hc hPr
  Uloc_g := fun i v hv x hx => by
    refine levLoc_of_princ hc n (Pr.vT u) Pr.vGs Λ.grp v (Pr.g i) ?_ ?_ x hx.1 hx.2
    · intro hT
      have h1 : (Pr.T u : 𝓞 X.F) ∈ v.asIdeal :=
        (mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hT
      exact rls_T_notUnder hPr u v h1 ((th_plUnder_vGs hc hPr v).2 (by fin_cases i; exact Or.inl hv; exact Or.inr hv))
    · intro w _ hov
      have : (Pr.g i : 𝓞 X.F) ∈ w.asIdeal.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) := hov ▸ hv
      rwa [Ideal.mem_comap, map_natCast] at this
  UlocAlt := hK

def levPack (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) :
    LevPack hc H.n' H.J Pr.g (Pr.T u) H.f H.bad (fun c => MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) H.lat := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact levPack₁ hc hX hPr σ₀ u Λ c₀ s hS hs hK

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

def LevPack.toStep (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.StepLevel hc S gp T f where
  Lb := P.lev.Lb
  Lb_fin := P.lev.Lb_fin
  Lb_span := P.lev.Lb_span
  Lb_int := fun x hx => Submodule.subset_span (P.lev.Lb_int x hx)
  Lb_dual := fun y hy => by
    refine Submodule.span_induction (p := fun y _ => (T : E) • y ∈ P.lev.Lb) (fun y hy => P.lev.Lb_dual y hy) ?_ ?_ ?_ hy
    · rw [smul_zero]; exact zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact add_mem ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  Lb_index := P.lev.Lb_index
  Uloc := P.lev.Uloc
  Uloc_lev := P.lev.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT => P.lev.Uloc_hyp v (fun hb => ((P.bad_iff v).1 hb).elim h0 h1) hT
  Uloc_g := P.Uloc_g
  UlocAlt := P.UlocAlt
  U := P.lev.U
  U_eq := P.lev.U_eq

def LevPack.toCls (P : LevPack hc S.rank S.gram gp T f bad stab fun c => Formalism.L2.Herm.crdLat S (lat c)) :
    Formalism.L2.Herm.ClassTie hc S P.toStep.Lb P.toStep.U stab lat where
  y := P.cls.y
  y_bij := P.cls.y_bij
  y_lat := P.cls.y_lat
  stabI := P.cls.stabI
  stabI_inj := P.cls.stabI_inj
  stabI_range := fun c γ => P.cls.stabI_range c γ.1 γ.2

end Repack

end Formalism.L2.Col
end
end

section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_chrOk_holds (hc : cst.Ok) {i : ℕ} {w : rowSG Pr sel mu} (hw : w.1 ∉ Pr.vGs) (hd : TwDegOne X w.1) (hi : i + 2 ≤ R.m)
    (hD : i + 1 ≤ cst.D w) {hal : AutY X R i} {h : AutY X R (i + 1)} (hba : TwBdd (Pr := Pr) i w.1 hal)
    (hbb : TwBdd (Pr := Pr) (i + 1) w.1 h) (hint : prCat (Pr := Pr) cst.sharp (i + 1) w.1 h ≤ GLint X.E (R.N (i + 1)) w.1)
    (hne : FiniteSumNonzeroLargeDepth Ch sel mu cst i w hal h) : TwChrOk Ch sel mu cst (i + 1) w h :=
  clXQ_chrOk_of cq_covT hc hw hd hi hD hba hbb hint hne

end Formalism.L2.Col
end
end
