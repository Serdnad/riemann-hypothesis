module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle010
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.SubstSPtrue
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.NormalDegreeZeroMul
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle016
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle001
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockR
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle005
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.Bundle002
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

def symP (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K) (hrk : r ≤ m + 1)
    (F : Frames n' r) (c' Q : ℕ) (P : RRing O n' (r + K)) : MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) P * SPR O p F hrk c' Q)

def XiAtP (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O] (w : O) {m : ℕ} (r : ℕ)
    (TT : Finset (Fin n')) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1)
    (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (c0 cP κ : ℕ) (bD : ℝ) {nb : ℕ} (B : Fin nb → RRing O n' (r + K)) : Prop :=
  ∃ DX : ℕ, (DX : ℝ) ≤ bD ∧
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => symP p O hk hrk Fr cP (p ^ G') (B b))) →
      HasMultideg G d → InWj w G 0 → ¬ InWj w G 1 →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock G (∑ q, sig q) / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O))

def XiStepP (C CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
        XiAtP p w r TT (dT TT lam0) (flatDeg lam0) K hk hrk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0
          (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0))
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) B

def RestXiP (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → XiStepP C CDf CLa


theorem xiStepN_of_P (C CD CLa : ℝ) (hP : XiStepP C CD CLa) : XiStepN C CD CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hw : algebraMap O (KK O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero
  obtain ⟨DX, hDX, hP⟩ := hP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk hrk F hF
    E' hE' nb B hB hli hc
  refine ⟨DX, hDX, fun F1 h1 h2 h3 => ?_⟩
  refine hP (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) ?_ ?_ ?_ ?_
  · rw [subst_eq_Lin]
    refine Lin_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) TT c0 _ _ ?_ _ h1
    intro f0 hf0
    induction hf0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      refine Submodule.subset_span ⟨b, ?_⟩
      show symP p O hk hrk F _ _ (B b) = _
      rw [← subst_eq_Lin, hFsB b]
      unfold symB toK symP
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, map_mul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · exact substPol p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ F1.2
  · have h4 : Θ' F1 ∈ scale (algebraMap O Kf w ^ ((0 : ℕ) : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) := by
      rw [← hΘeq]
      exact mem_scale.2 ⟨Θ F1, h2, by simp⟩
    exact (hΘ1.2 g hg e hbasis F1 0).2 h4
  · intro hI
    apply h3
    have h4 := (hΘ1.2 g hg e hbasis F1 1).1 hI
    rw [← hΘeq] at h4
    simpa using h4

theorem restXiN_of_P (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hP : RestXiP D CLa Ck Crk Cdeg CH CE C6 C18) : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA h14b
  obtain ⟨CDf, C₁, h1, h2, h3⟩ := hP hA h14b
  exact ⟨CDf, C₁, h1, h2, fun C hC => xiStepN_of_P C CDf CLa (h3 C hC)⟩

theorem restXi_of_P (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hP : RestXiP D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  restXi_of_N D CLa Ck Crk Cdeg CH CE C6 C18 (restXiN_of_P D CLa Ck Crk Cdeg CH CE C6 C18 hP)

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.MainNotions.G.LatticeSystems (lb_D lb_D_det kp_lamAt_antitone)

section Tensor

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {S : Type} [Fintype S] [DecidableEq S] {k n : ℕ}

theorem tensor_onto (A B M : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (hM : ∀ s, M s ≤ Submodule.span R {X | ∃ F ∈ A s, ∃ G ∈ B s, X = F * G}) :
    tensorLat R K M ≤ Submodule.span R {X | ∃ P ∈ tensorLat R K A, ∃ Q ∈ tensorLat R K B, X = P * Q} :=
  _root_.UpperTheory.Reformulated.B.product_first_partition.tensor_onto A B M hM

end Tensor

theorem ontoAll : OntoAll := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r d rest lam hlam hdr e he z hz
  have hw := w_ne_zero h
  have := h.frac_O
  have hfd : IsDominant (flW (m := m) d) := flW_dom _
  have hAr : Ar r lam = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _
  obtain ⟨gs, hgs, _, h2, _⟩ := Formalism.L2.G.Model.edgeLat h m r e he
  have hΛ : ∀ s : Fin n', ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, IsUnit g.det ∧
      LeAt p ι σ w s.val e = colSpan O g := fun s =>
    ⟨_, by rw [Matrix.det_mul]; exact (hgs _).mul (lb_D_det _ _ _ hw), h2 s.val⟩
  set cw : Kf := algebraMap O Kf w with hcw
  set Sp := Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e,
    ∃ β ∈ Re p ι σ w r rest e, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)} with hSp
  obtain ⟨z0, hz0, rfl⟩ := mem_scale.1 hz
  have hz0' : ((z0 : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O lam (fun s => LeAt p ι σ w s.val e) := hz0
  have hten := tensor_onto (R := O) (fun s => H0 O m (lamAt (flW (m := m) d) s) (LeAt p ι σ w s.val e))
    (fun s => H0 O m (lamAt rest s) (LeAt p ι σ w s.val e)) (fun s => H0 O m (lamAt lam s) (LeAt p ι σ w s.val e))
    (fun s => by
      rw [hlam, lamAt_add]
      exact le_of_eq (Formalism.L2.G.Model.cartanOnto_proved O Kf m _ _ _ (hΛ s) (kp_lamAt_antitone _ hfd s)
        (kp_lamAt_antitone _ hdr s))) hz0'
  have key : ∀ x ∈ Submodule.span O {X | ∃ P ∈ Hten O (flW (m := m) d) (fun s => LeAt p ι σ w s.val e),
      ∃ Q ∈ Hten O rest (fun s => LeAt p ι σ w s.val e), X = P * Q},
      ∃ hx : x ∈ Vsp Kf lam, cw ^ (-Ar r lam) • (⟨x, hx⟩ : Vsp Kf lam) ∈ Sp := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, hP, Q, hQ, rfl⟩ := hx
      have hPV := Hten_le_V hfd _ hΛ P hP
      have hQV := Hten_le_V hdr _ hΛ Q hQ
      refine ⟨V_mul Kf hlam hfd hdr hPV hQV, Submodule.subset_span
        ⟨cw ^ (-Ar r (flW (m := m) d)) • ⟨P, hPV⟩, mem_scale.2 ⟨⟨P, hPV⟩, hP, rfl⟩,
          cw ^ (-Ar r rest) • ⟨Q, hQV⟩, mem_scale.2 ⟨⟨Q, hQV⟩, hQ, rfl⟩, ?_⟩⟩
      simp only [Submodule.coe_smul]
      rw [smul_mul_smul_comm, ← zpow_add₀ hw, hAr]
      congr 2
      ring
    | zero => exact ⟨Submodule.zero_mem _, by
        have : (⟨0, Submodule.zero_mem _⟩ : Vsp Kf lam) = 0 := rfl
        rw [this, smul_zero]; exact Submodule.zero_mem _⟩
    | add a b _ _ ha hb =>
      obtain ⟨ha1, ha2⟩ := ha
      obtain ⟨hb1, hb2⟩ := hb
      refine ⟨Submodule.add_mem _ ha1 hb1, ?_⟩
      have : (⟨a + b, Submodule.add_mem _ ha1 hb1⟩ : Vsp Kf lam) = ⟨a, ha1⟩ + ⟨b, hb1⟩ := rfl
      rw [this, smul_add]
      exact Submodule.add_mem _ ha2 hb2
    | smul t a _ ha =>
      obtain ⟨ha1, ha2⟩ := ha
      have hta : t • a ∈ Vsp Kf lam := by
        rw [← algebraMap_smul Kf t a]
        exact Submodule.smul_mem _ _ ha1
      refine ⟨hta, ?_⟩
      have : (⟨t • a, hta⟩ : Vsp Kf lam) = t • ⟨a, ha1⟩ := rfl
      rw [this, smul_comm]
      exact Submodule.smul_mem _ _ ha2
  obtain ⟨hx, hmem⟩ := key _ hten
  exact hmem

theorem restCloudB_of_two (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) (hop : RestTSOp D CLa Ck Crk Cdeg) (hsz : RestSize) :
    RestCloudB D CLa Ck Crk Cdeg :=
  restCloudB_of_three D CLa Ck Crk Cdeg hop hsz ontoAll

end Formalism.MainNotions.TestSideCounting
end
end

section

noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial
open Formalism.L2.G.Model.TS (fockR)

def RestTSX : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (X : Fin n' → Fin (m + 1) → ℤ), IsDominant X →
    ∃ (Ψ : Module.Dual Kf ↥(Vsp Kf X) ≃ₗ[Kf] ↥(Vsp Kf X)) (c : Kf), c ≠ 0 ∧
      TSProp p n' (W := W) (O := O) ι σ w r X Ψ ∧
      ∀ y u : Vsp Kf X, Ψ.symm y u =
        c * fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
          (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)

def OpFAt {n' : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {m : ℕ} (TT : Finset (Fin n'))
    (d : Fin n' → ℕ) (rest : Fin n' → Fin (m + 1) → ℤ) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∀ (κ : Kf) (β s : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)),
    ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
      (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
        OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
      ∀ Y : Vsp Kf (flW (m := m) d),
        fockR ((Θ F' : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
            (Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          κ * fockR (((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
            ((Y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) *
              (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))

def OpFStep (C : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    ∀ hSet : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w,
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ (hm : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq), IsUnit hm.det →
      ∀ Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) (dT TT lam0)).restrictScalars O) ≃ₗ[O]
      ↥(Vsp Kf (flW (m := m) (dT TT lam0))),
        IsTrueTheta hSet.1 (dT TT lam0) (flW (dT TT lam0)) (vecE n') hm Θ →
        OpFAt TT (dT TT lam0) (topW TT (restW TT lam0)) c0 Θ

def RestOpF : Prop := ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → OpFStep C

theorem tsOpAt_of {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hX : RestTSX)
    {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ)
    (hlam : IsDominant lam) (c0 : ℕ)
    (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hOp : OpFAt TT d rest c0 Θ) : TSOpAt p n' (W := W) ι σ w r TT d rest lam c0 Θ := by
  obtain ⟨Ψ0, a0, ha0, t0, f0⟩ := hX p n' W Qq O Kf ι σ j w hS m r lam hlam
  obtain ⟨Ψf, af, haf, tf, ff⟩ := hX p n' W Qq O Kf ι σ j w hS m r (flW d) (flW_dom d)
  refine ⟨Ψ0, Ψf, t0, tf, ?_⟩
  intro β F s u hu
  obtain ⟨F', h1, h2⟩ := hOp ((p : Kf) ^ Ar r rest * ((p : Kf) ^ kap1 p lam * a0) / af) β s F
  refine ⟨F', h1, ?_⟩
  intro T z hz
  have e1 : T (Θ F') = af * fockR ((Θ F' : Vsp Kf (flW (m := m) d)) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (Ψf T : Vsp Kf (flW (m := m) d)) := by
    rw [← ff (Ψf T) (Θ F'), LinearEquiv.symm_apply_apply]
  rw [e1, h2 (Ψf T), f0 z u, hu, hz]
  field_simp

theorem restTSOp_of (hX : RestTSX) (hOp : RestOpF) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestTSOp D CLa Ck Crk Cdeg := by
  intro _
  obtain ⟨C₁, hC1, h⟩ := hOp
  refine ⟨C₁, hC1, fun C hC => ?_⟩
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ
    e he htgt hm g hhm hg hbasis Θ hΘ
  have hdom : IsDominant lam0 := H.2.2.2.2.1.2.1
  exact tsOpAt_of hSet.1 hX r TT (dT TT lam0) _ _ (topW_dom TT hdom) c0 Θ
    (h C hC p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de hh x lam0 aT bT a Y cpp c0 Dp cStar hSet H hm hhm Θ hΘ)

end Formalism.MainNotions.TestSideCounting
end
end
