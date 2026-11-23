module

public import Formalism.SharpRestriction.GrowthBounds.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle002
public import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.DvdOfAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

def vecE (n' : ℕ) : Fin n' → Bool := fun s => decide (Even s.val)

def flW {n' m : ℕ} (d : Fin n' → ℕ) : Fin n' → Fin (m + 1) → ℤ := fun s => Pi.single 0 (d s : ℤ)

theorem isFlat_flW {n' m : ℕ} (d : Fin n' → ℕ) : IsFlat (m := m) (vecE n') d (flW d) := by
  intro s
  by_cases hs : Even s.val
  · simp [lamAt, vecE, flW, hs]
  · funext i
    simp only [lamAt, vecE, flW, hs, if_false, decide_false, Bool.false_eq_true]
    by_cases hi : i = Fin.last m
    · subst hi
      simp
    · have hr : i.rev ≠ 0 := by
        intro h0
        apply hi
        rw [← Fin.rev_rev i, h0, Fin.rev_zero]
      simp [hi, hr]

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_shift (c : Kf) (hc : c ≠ 0) (a b : ℕ) (M : Submodule O X) {x : X}
    (hx : x ∈ scale (c ^ ((a + b : ℕ) : ℤ)) M) : (c ^ (-(a : ℤ))) • x ∈ scale (c ^ (b : ℤ)) M := by
  rw [mem_scale] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, hy, ?_⟩
  rw [smul_smul, ← zpow_add₀ hc, show -(a : ℤ) + ((a + b : ℕ) : ℤ) = b by push_cast; ring]

end Scale

def IsFlatIdent {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) (φ : WF p n' ≃+* W) [Algebra (WF p n') O] {m : ℕ} (r : ℕ)
    (d : Fin n' → ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (vec : Fin n' → Bool)
    (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf lam0)) : Prop :=
  (∀ F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
    InA (O := O) (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ↔
    Θ F ∈ HL (O := O) ι σ lam0 (colSpan W h)) ∧
  ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
      ∀ (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (i : ℕ),
        InWjRg p n' O w r (flatLetters vec) g
          (F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) i ↔
        Θ F ∈ scale (algebraMap O Kf w ^ (i : ℤ)) (Re p ι σ w r lam0 e)

theorem flatSrc (hEP : EdgePlane) (p n' : ℕ) [Fact p.Prime] (W Qq O Kf : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field Kf] [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (hS : HidaSetting p n' W Qq O Kf ι σ j w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (m r : ℕ) (d : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det) :
    letI : Algebra (WF p n') O := algOfIdent j φ
    ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)),
      IsFlatIdent ι σ w φ r d (flW d) (vecE n') h Θ →
    ∀ g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'), IsGLW g →
    ∀ e : Edge W Qq (m + 1), IsEdgeBasis p r e (h * ((matQ φ g)⁻¹).transpose) →
    ∀ (c' o : ℕ) (sig : MvPolynomial (TV n' (m + 1)) (KK O))
      (Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
      HasMultideg sig d → subst p n' O w n' r g (Fsig : MvPolynomial (TV n' (m + 1)) (KK O)) = sig →
      Realisable p n' w n' r g c' o sig →
      ∃ Fv : Vsp Kf (flW (m := m) d),
        Fv ∈ scale (algebraMap O Kf w ^ (-(o : ℤ))) (HL (O := O) ι σ (flW d) (colSpan W h)) ∧
        Fv - Θ Fsig ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e) ∧
        ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = colSpan W h → e' ≠ e →
          Fv ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r (flW d) e') := by
  let _ : Algebra (WF p n') O := algOfIdent j φ
  intro Θ hΘ g hg e he c' o sig Fsig hsig hsub hreal
  obtain ⟨F, hFA, hFdeg, hFW, hFo⟩ := hreal
  obtain ⟨F', rfl⟩ : ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) = F := ⟨⟨F, hFdeg d hsig⟩, rfl⟩
  have hc0 : algebraMap O Kf w ≠ 0 := w_ne_zero hS
  obtain ⟨hE1, -, hE3⟩ := hEP p n' W Qq O Kf ι σ j w hS φ hφ m r h hh
  refine ⟨(algebraMap O Kf w ^ (-(o : ℤ))) • Θ F', ?_, ?_, ?_⟩
  · exact mem_scale.mpr ⟨Θ F', (hΘ.1 F').mp hFA, rfl⟩
  · have key : InWjRg p n' O w r (flatLetters (vecE n')) g
        ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) (o + c') := by
      show InWj w (subst p n' O w n' r g _) (o + c')
      have hx : ((F' - (w ^ o) • Fsig : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) :
          MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) =
          (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) -
            C (algebraMap O (KK O) (w ^ o)) * (Fsig : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) := by
        rw [Submodule.coe_sub, Submodule.coe_smul_of_tower, ← algebraMap_smul (KK O), smul_eq_C_mul]
      rw [hx, map_sub, map_mul, hsub, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        MvPolynomial.algebraMap_eq]
      exact hFW
    have hmem := scale_shift (algebraMap O Kf w) hc0 o c' _ ((hΘ.2 g hg e he _ (o + c')).mp key)
    have heq : (algebraMap O Kf w ^ (-(o : ℤ))) • Θ (F' - (w ^ o) • Fsig) =
        (algebraMap O Kf w ^ (-(o : ℤ))) • Θ F' - Θ Fsig := by
      rw [show Θ (F' - (w ^ o) • Fsig) = Θ F' - Θ ((w ^ o) • Fsig) from Θ.map_sub _ _,
        show Θ ((w ^ o) • Fsig) = (w ^ o) • Θ Fsig from Θ.map_smul _ _,
        ← algebraMap_smul Kf (w ^ o), smul_sub, smul_smul, map_pow,
        ← zpow_natCast, ← zpow_add₀ hc0, neg_add_cancel, zpow_zero, one_smul]
    rwa [heq] at hmem
  · intro e' he' hsrc hne
    obtain ⟨g', hg', hb'⟩ := hE1 e' he' hsrc
    have hrat : ratPlane p n' r g' ≠ ratPlane p n' r g := fun hr =>
      hne ((hE3 g' g e' e hg' hg hb' he).mpr hr)
    exact scale_shift (algebraMap O Kf w) hc0 o c' _
      ((hΘ.2 g' hg' e' hb' F' (o + c')).mp (hFo g' hg' hrat))

end Formalism.MainNotions.Pf14
end
end

section

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

section Scale

variable {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
  [IsScalarTower O Kf X]

theorem scale_zpow_mono (w : O) (hw : algebraMap O Kf w ≠ 0) {a b : ℤ} (hab : b ≤ a) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ a) M ≤ scale (algebraMap O Kf w ^ b) M := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_scale.1 hx
  refine mem_scale.2 ⟨w ^ (a - b).toNat • y, M.smul_mem _ hy, ?_⟩
  rw [← algebraMap_smul Kf (w ^ (a - b).toNat) y, smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
  congr 2
  rw [Int.toNat_of_nonneg (by omega)]
  ring

theorem scale_mono (c : Kf) {M N : Submodule O X} (h : M ≤ N) : scale c M ≤ scale c N :=
  Submodule.map_mono h

end Scale

section Be

variable {Kf : Type} [Field Kf] {n' m : ℕ}

theorem be_add_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (F F' : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (F + F') G = be p r lam0 F G + be p r lam0 F' G := by
  unfold be
  rw [smul_add, map_add (f := _)]

theorem be_smulK_left (p r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (c : Kf) (F : Vsp Kf lam0)
    (G : Module.Dual Kf (Vsp Kf lam0)) : be p r lam0 (c • F) G = c * be p r lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

end Be

theorem edgeFamOf : EdgeFamOf := by
  intro D hM hBP hInc p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w hS m r fl rest lam0 hnu h1 h2 e he nb n2 T oS tT D1
    cStar c' hc' hD Fvb Sy sh hF1 hF2 hF3 hSy hsh hT
  have hw := w_ne_zero hS
  have hdom : IsDominant lam0 := by
    rw [hnu]
    exact isDominant_add h1 h2
  let eqv : Fin nb × Fin n2 ≃ Fin (nb * n2) := finProdFinEquiv
  let Fs : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Fvb x.1) (sh x.2)
  let Ss : Fin nb × Fin n2 → Vsp Kf lam0 := fun x => mulV hnu h1 h2 (Sy x.1) (sh x.2)
  have hdiff : ∀ x, Fs x - Ss x ∈ scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) := by
    intro x
    have hz : ((Fs x - Ss x : Vsp Kf lam0) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
        ((Fvb x.1 - Sy x.1 : Vsp Kf fl) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
          ((sh x.2 : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      simp only [Fs, Ss, AddSubgroupClass.coe_sub, mulV_coe, sub_mul]
    have h0 : sh x.2 ∈ scale (algebraMap O Kf w ^ (0 : ℤ)) (Re p ι σ w r rest e) := by
      rw [zpow_zero]
      exact mem_scale.2 ⟨_, (hsh x.2).1, one_smul _ _⟩
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e (c' : ℤ) 0 hz (hF2 x.1) h0
    rwa [add_zero] at h3
  have hSs : ∀ x, Ss x ∈ Re p ι σ w r lam0 e := fun x =>
    edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hnu h1 h2 e (z := Ss x) rfl (hSy x.1) (hsh x.2).1
  refine ⟨fun i => Fs (eqv.symm i), ?_, ?_, ?_⟩
  · intro i
    constructor
    · have h3 := HL_mul (O := O) D hM ι σ hnu h1 h2 e.src (algebraMap O Kf w) hw (-(T : ℤ)) (-(oS : ℤ))
        (z := Fs (eqv.symm i)) rfl (hF1 _) (hsh _).2
      have e1 : (-(T : ℤ)) + (-(oS : ℤ)) = -((T + oS : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [e1] at h3
    · have e2 : Fs (eqv.symm i) = Ss (eqv.symm i) + (Fs (eqv.symm i) - Ss (eqv.symm i)) := by abel
      show Fs (eqv.symm i) ∈ Re p ι σ w r lam0 e
      rw [e2]
      exact Submodule.add_mem _ (hSs _) (scale_pos_le w c' _ (hdiff _))
  · intro i e' he' hsrc hne
    have hI := (hInc p n' W Qq O Kf ι σ j w hS m r rest h2 e' he').1
    have hs : sh (eqv.symm i).2 ∈ scale (algebraMap O Kf w ^ (-(oS : ℤ))) (Re p ι σ w r rest e') := by
      apply scale_mono _ hI
      rw [hsrc]
      exact (hsh _).2
    have h3 := Re_mul D hM p ι σ w hw r hnu h1 h2 e' (c' : ℤ) (-(oS : ℤ)) (z := Fs (eqv.symm i)) rfl
      (hF3 _ e' he' hsrc hne) hs
    exact scale_zpow_mono w hw (by omega) _ h3
  · rintro c ⟨i0, hi0⟩
    obtain ⟨G, hG1, hG2, hG3, ⟨a, b, ha, hab⟩⟩ := hT (fun x => c (eqv x))
      ⟨eqv.symm i0, by simpa using hi0⟩
    refine ⟨G, hG1, hG2, hG3, ?_⟩
    have e1 : (∑ i, c i • Fs (eqv.symm i)) =
        (∑ x, c (eqv x) • Ss x) + ∑ x, c (eqv x) • (Fs x - Ss x) := by
      rw [← Finset.sum_add_distrib, ← Equiv.sum_comp eqv]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Equiv.symm_apply_apply, ← smul_add]
      congr 1
      abel
    have hE : (∑ x, c (eqv x) • (Fs x - Ss x)) ∈
        scale (algebraMap O Kf w ^ (c' : ℤ)) (Re p ι σ w r lam0 e) :=
      Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hdiff x)
    obtain ⟨y, hy, hyE⟩ := mem_scale.1 hE
    obtain ⟨z, hz⟩ := ((hBP p n' W Qq O Kf ι σ j w hS m r lam0 hdom e he).1 G).1 hG2 y hy
    have hwc : w ^ c' = (p : O) ^ (D1 + 1) * w ^ (c' - 2 * (D1 + 1)) := by
      rw [← hS.w_sq, ← pow_mul, ← pow_add]
      congr 1
      omega
    obtain ⟨b', hb'⟩ := dvd_of_add (p : O) (p_nonunit hS) D1 a (w ^ (c' - 2 * (D1 + 1)) * z) ⟨b, hab.symm⟩
    refine ⟨a + (p : O) ^ (D1 + 1) * (w ^ (c' - 2 * (D1 + 1)) * z), b', ?_, hb'.symm⟩
    show be p r lam0 (∑ i, c i • Fs (eqv.symm i)) G = _
    rw [e1, be_add_left, ha, ← hyE, be_smulK_left, ← hz, zpow_natCast, ← map_pow, hwc]
    simp only [map_add (f := _), map_mul]
    ring

end Formalism.MainNotions.Pf14
end
end
