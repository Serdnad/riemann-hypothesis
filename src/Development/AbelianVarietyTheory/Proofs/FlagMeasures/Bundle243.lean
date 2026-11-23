module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle224
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle211
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle232
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle234
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))

lemma cjO {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Gen : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

variable {Fr L}

lemma gen_mem {v : V} (hv : v ∈ Gen Fr L) : v ∈ Fr.LamStd L := Submodule.subset_span hv

lemma smulO {c : E} (hc : c ∈ M.L.O) {v : V} (hv : v ∈ Fr.LamStd L) : c • v ∈ Fr.LamStd L :=
  (Fr.LamStd L).smul_mem (⟨c, hc⟩ : M.L.O) hv

variable (Fr L)

lemma e_gen (a : Fin r) : Fr.e a ∈ Gen Fr L := by
  have h1 : ∀ b, H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := fun b => Fr.h_es a b
  have h2 : ∀ b, H.h (Fr.e a) (Fr.e b) = 0 := fun b => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last a))
  refine ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
  · rw [h1]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · rw [h2]; exact M.L.O.zero_mem
  · simp only [FrameD.prF, h1, h2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Finset.sum_const_zero, sub_self, sub_zero, ZeroMemClass.coe_zero]
  · rw [map_zero]; exact L.zero_mem

lemma es_gen (k : Fin r) : Fr.es k ∈ Gen Fr L := by
  have h1 : ∀ b, H.h (Fr.es k) (Fr.es b) = 0 := fun b => Fr.h_ss k b
  have h2 : ∀ b, H.h (Fr.es k) (Fr.e b) = if b = k then 1 else 0 := fun b => by
    rw [h_right H, show Fr.e b = Fr.f b.castSucc from rfl, Fr.h_es]
    split_ifs <;> simp
  refine ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
  · rw [h1]; exact M.L.O.zero_mem
  · rw [h2]; split_ifs
    · exact M.L.O.one_mem
    · exact M.L.O.zero_mem
  · simp only [FrameD.prF, h1, h2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Finset.sum_const_zero, sub_self, sub_zero, ZeroMemClass.coe_zero]
  · rw [map_zero]; exact L.zero_mem

lemma comb_mem (β : Fin r → E) (hβ : ∀ a, β a ∈ M.L.O) :
    (∑ a, β a • Fr.e a) ∈ Fr.LamStd L ∧ ∀ v ∈ Gen Fr L, H.h v (∑ a, β a • Fr.e a) ∈ M.L.O := by
  refine ⟨Submodule.sum_mem _ fun a _ => smulO (hβ a) (gen_mem (e_gen Fr L a)), fun v hv => ?_⟩
  rw [h_right H]
  apply cjO
  have hl : H.h (∑ a, β a • Fr.e a) v = ∑ a, β a * H.h (Fr.e a) v := by
    show (lf H v) _ = _

    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    rfl
  rw [hl]
  exact M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hβ a) (by rw [h_right H]; exact cjO (hv.2.1 a))

variable {Fr L}

lemma pres_of_gen (g : V →ₗ[E] V) (h : ∀ v ∈ Gen Fr L, g v ∈ Fr.LamStd L) :
    ∀ v ∈ Fr.LamStd L, g v ∈ Fr.LamStd L := by
  have : Fr.LamStd L ≤ (Fr.LamStd L).comap (g.restrictScalars M.L.O) :=
    Submodule.span_le.2 fun v hv => h v hv
  exact fun v hv => this hv

lemma eich_gen {x : V} (hxl : x ∈ Fr.LamStd L) (hxh : ∀ v ∈ Gen Fr L, H.h v x ∈ M.L.O) (k : Fin r) :
    ∀ y ∈ Gen Fr L, eichL H x (Fr.es k) 0 y ∈ Fr.LamStd L := by
  intro y hy
  show eichF H x (Fr.es k) 0 y ∈ _
  unfold eichF
  rw [map_zero, zero_mul, zero_smul, add_zero]
  exact sub_mem (add_mem (gen_mem hy) (smulO (hy.1 k) hxl)) (smulO (hxh y hy) (gen_mem (es_gen Fr L k)))

end GlobalTheory.LocOver.UnipLevi

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
  (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f))

lemma levi_lam (u : Fin r → V) (hu : ∀ c, u c ∈ Fr.Fj c.val) (hul : ∀ c, u c ∈ Fr.LamStd L)
    (huh : ∀ c, ∀ v ∈ Gen Fr L, H.h v (u c) ∈ M.L.O) :
    ∀ k, k ≤ r → ∃ n ∈ NUg Fr, (∀ c : Fin r, n (Fr.f c.castSucc) =
      Fr.f c.castSucc + if c.val < k then u c else 0) ∧ n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧
      ∀ v ∈ Fr.LamStd L, n v ∈ Fr.LamStd L ∧ n⁻¹ v ∈ Fr.LamStd L := by
  intro k
  induction k with
  | zero => intro _; exact ⟨1, (NUg Fr).one_mem, fun c => by simp, by simp, fun v hv => by simpa using hv⟩
  | succ k ih =>
    intro hk
    obtain ⟨n, hn, hne, hnz, hnl⟩ := ih (by omega)
    set kk : Fin r := ⟨k, by omega⟩ with hkk
    have hx : u kk ∈ H.X Fr.f := Fj_le_X Fr _ (hu kk)
    have hxv : H.h (u kk) (Fr.es kk) = 0 := Fj_es Fr kk.val kk le_rfl _ (hu kk)
    have hc : 2 * algebraMap F E (0 : F) + H.h (Fr.es kk) (Fr.es kk) = 0 := by
      rw [Fr.h_ss, map_zero]; ring
    have hM := eich_mem Fr hx hxv hc (fun a => by
      rw [Fr.h_es]
      by_cases hak : a = kk
      · subst hak; simpa using hu _
      · simp [hak])
    set g := eichE H (X_iso Fr (u kk) hx (u kk) hx) hxv hc with hg
    have hgl : ∀ v ∈ Fr.LamStd L, g v ∈ Fr.LamStd L ∧ g⁻¹ v ∈ Fr.LamStd L := by
      intro v hv
      refine ⟨pres_of_gen _ (eich_gen (hul kk) (huh kk) kk) v hv, ?_⟩
      have hxh' : ∀ y ∈ Gen Fr L, H.h y (-u kk) ∈ M.L.O := fun y hy => by
        rw [h_neg_right]; exact M.L.O.neg_mem (huh kk y hy)
      exact pres_of_gen _ (eich_gen (neg_mem (hul kk)) hxh' kk) v hv
    refine ⟨g * n, mul_mem hM hn, fun c => ?_, ?_, fun v hv => ?_⟩
    · rw [LinearEquiv.mul_apply, hne c, hg, eichE_apply]
      have hcx : H.h (Fr.f c.castSucc) (u kk) = 0 :=
        X_iso Fr _ (Fj_le_X Fr (c.val + 1) (e_mem Fr c)) _ hx
      by_cases hck : c.val < k
      · have hfix : eichF H (u kk) (Fr.es kk) 0 (u c) = u c :=
          eich_fix H _ _ _ _ (Fj_es Fr c.val kk (by simp [hkk]; omega) _ (hu c))
            (X_iso Fr _ (Fj_le_X Fr _ (hu c)) _ hx)
        have hne' : c ≠ kk := fun h => by subst h; simp [hkk] at hck
        have hadd : eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc + u c) =
            eichF H (u kk) (Fr.es kk) 0 (Fr.f c.castSucc) + eichF H (u kk) (Fr.es kk) 0 (u c) :=
          (eichL H (u kk) (Fr.es kk) 0).map_add _ _
        have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hne']
        rw [if_pos hck, if_pos (by omega), hadd, hfix]
        simp [eichF, hcx, hes]
      · rw [if_neg hck]
        by_cases hce : c = kk
        · subst hce
          have h1 : H.h (Fr.f kk.castSucc) (Fr.es kk) = 1 := by rw [Fr.h_es, if_pos rfl]
          have : kk.val < k + 1 := by simp [hkk]
          rw [if_pos this]
          simp [eichF, hcx, h1]
        · have : ¬ c.val < k + 1 := fun h => hce (Fin.ext (by simp [hkk]; omega))
          have hes : H.h (Fr.f c.castSucc) (Fr.es kk) = 0 := by rw [Fr.h_es, if_neg hce]
          rw [if_neg this]
          simp [eichF, hcx, hes]
    · rw [LinearEquiv.mul_apply, hnz, hg, eichE_apply]
      exact eich_fix H _ _ _ _ (z_es Fr kk) (z_X Fr _ hx)
    · refine ⟨?_, ?_⟩
      · rw [LinearEquiv.mul_apply]
        exact (hgl _ (hnl v hv).1).1
      · rw [mul_inv_rev, LinearEquiv.mul_apply]
        exact (hnl _ (hgl v hv).2).2

end GlobalTheory.LocOver.UnipLevi

namespace GlobalTheory.LocOver.UnipLevi

open GlobalTheory.LocOver.UnipOnto

theorem levi_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), ∀ A : Matrix (Fin (r + 1)) (Fin (r + 1)) E, Uni A →
    (∀ a b, A a b ∈ M.L.O) → ∃ n ∈ Fr.N, (∀ c : Fin r, n (Fr.f c.castSucc) = ∑ a, A a c.castSucc • Fr.f a) ∧
      n (Fr.f (Fin.last r)) = Fr.f (Fin.last r) ∧ img n (Fr.LamStd L) = Fr.LamStd L := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r Fr L A hA hAO
  set u : Fin r → V := fun c => (∑ a, A a c.castSucc • Fr.f a) - Fr.f c.castSucc with hud
  have hm := mem_of_tri Fr.f (fun b => ∑ a, A a b • Fr.f a) ⟨A, hA, fun b => rfl⟩
  have hu : ∀ c : Fin r, u c ∈ Fr.Fj c.val := fun c =>
    spanf_le Fr c.val c.isLt.le (by simpa using hm c.castSucc)
  have hdec : ∀ c : Fin r, u c = (∑ a : Fin r, A a.castSucc c.castSucc • Fr.e a) - Fr.e c := by
    intro c
    simp only [hud]
    rw [Fin.sum_univ_castSucc, hA.1 _ _ (Fin.castSucc_lt_last c), zero_smul, add_zero]
    rfl
  have hul : ∀ c, u c ∈ Fr.LamStd L := fun c => by
    rw [hdec]
    exact sub_mem (comb_mem Fr L _ (fun a => hAO _ _)).1 (gen_mem (e_gen Fr L c))
  have huh : ∀ c, ∀ v ∈ Gen Fr L, H.h v (u c) ∈ M.L.O := fun c v hv => by
    rw [hdec, h_sub_right]
    exact M.L.O.sub_mem ((comb_mem Fr L _ (fun a => hAO _ _)).2 v hv) (hv.2.1 c)
  obtain ⟨n, hn, hne, hnz, hnl⟩ := levi_lam Fr L u hu hul huh r le_rfl
  refine ⟨n, by rw [N_eq]; exact hn, fun c => ?_, hnz, ?_⟩
  · rw [hne c, if_pos c.isLt]
    exact add_sub_cancel _ _
  · apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hnl v hv).1
    · intro v hv
      refine ⟨n⁻¹ v, (hnl v hv).2, ?_⟩
      show n (n⁻¹ v) = v
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl

end GlobalTheory.LocOver.UnipLevi
end
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.InnerDual

theorem unif_mem_maximal {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : Ideal L.O) (hm : m.IsMaximal) :
    (⟨algebraMap F E ϖ, (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).2 ϖ.2⟩ : L.O) ∈ m := by
  classical

  let φ : 𝒪[F] →+* L.O := ((algebraMap F E).comp (𝒪[F]).subtype).codRestrict L.O
    (fun c => (GlobalTheory.UnramOrder.algebraMap_mem_iff L c).2 c.2)
  have hcomp : (L.O.subtype).comp φ = algebraMap 𝒪[F] E := by
    ext c
    rfl
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨p, hp, hpx⟩ := (L.O_def x).1 x.2
    refine ⟨p, hp, Subtype.ext ?_⟩
    have key := Polynomial.hom_eval₂ p φ L.O.subtype x
    rw [hcomp] at key
    show L.O.subtype (Polynomial.eval₂ φ x p) = L.O.subtype 0
    rw [key, map_zero]
    exact hpx

  have := hm
  have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' φ hint m
  have h3 : ϖ ∈ m.comap φ := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact (IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit
  exact Ideal.mem_comap.1 h3

end GlobalTheory.LocOver.InnerDual

namespace GlobalTheory.LocOver.InnerDual


open GlobalTheory.LocOver.UnipOnto in
theorem exists_inner_lattice_vector_anisotropic' : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type}
    [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r)
    (L : Submodule M.L.O (H.Wb Fr.f)), Fr.IsInner L → ∃ y : ↥(H.perp (H.X Fr.f)),
    H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = 1 ∧ ∀ a, H.h (y : V) (Fr.es a) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr L hL
  have : IsNonarchimedeanLocalField F := hM.loc
  have : CharZero F := hM.char0
  classical
  obtain ⟨_hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : (xz : V) = Fr.f (Fin.last r) := hxz

  have hint : ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L →
      H.h (Fr.f (Fin.last r)) (y : V) ∈ M.L.O := by
    intro y hy
    have h0 := (hdual xz).1 hxzL y hy
    rwa [hz] at h0

  obtain ⟨I, hI⟩ : ∃ I : Ideal M.L.O, ∀ c : M.L.O, c ∈ I ↔
      ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧ H.h (Fr.f (Fin.last r)) (y : V) = (c : E) :=
    ⟨{ carrier := {c | ∃ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L ∧
          H.h (Fr.f (Fin.last r)) (y : V) = (c : E)}
       add_mem' := by
         rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hyb⟩
         refine ⟨y + y', by rw [map_add (f := _)]; exact L.add_mem hy hy', ?_⟩
         show H.h _ ((y : V) + (y' : V)) = (a : E) + (b : E)
         rw [h_add_right, hya, hyb]
       zero_mem' := by
         refine ⟨0, by rw [map_zero]; exact L.zero_mem, ?_⟩
         show H.h _ (0 : V) = 0
         exact h_zero_right H _
       smul_mem' := by
         rintro c a ⟨y, hy, hya⟩
         refine ⟨M.L.cj (c : E) • y, ?_, ?_⟩
         · rw [map_smul]
           exact L.smul_mem ⟨M.L.cj (c : E), GlobalTheory.UnramOrder.cj_mem M.L c.2⟩ hy
         · show H.h _ (M.L.cj (c : E) • (y : V)) = (c : E) * (a : E)
           rw [h_smul_right, M.L.cj_cj, hya] },
     fun c => Iff.rfl⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[F])
  have : IsPrincipalIdealRing M.L.O := (GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ).2.2.2.1
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)

  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨π, hπ⟩ := Submodule.IsPrincipal.principal m
    have hϖm := unif_mem_maximal M.L ϖ hϖ m hm
    rw [hπ, Submodule.mem_span_singleton] at hϖm
    obtain ⟨t, ht⟩ := hϖm
    have htE : (t : E) * (π : E) = algebraMap F E ϖ := congrArg Subtype.val ht
    obtain ⟨πi, hπi⟩ : ∃ πi : E, πi = (t : E) * algebraMap F E (ϖ : F)⁻¹ := ⟨_, rfl⟩
    have hinv : πi * (π : E) = 1 := by
      rw [hπi, mul_right_comm, htE, ← map_mul, mul_inv_cancel₀ hϖ0, map_one]
    have hvL : H.mkW Fr.f (πi • xz) ∈ L := by
      refine (hdual (πi • xz)).2 fun y hy => ?_
      have hyI : (⟨_, hint y hy⟩ : M.L.O) ∈ I := (hI _).2 ⟨y, hy, rfl⟩
      have hym := hIm hyI
      rw [hπ, Submodule.mem_span_singleton] at hym
      obtain ⟨s, hs⟩ := hym
      have hsE : (s : E) * (π : E) = H.h (Fr.f (Fin.last r)) (y : V) := congrArg Subtype.val hs
      show H.h (πi • (xz : V)) (y : V) ∈ M.L.O
      rw [H.h_smul_left, hz, ← hsE, mul_left_comm, hinv, mul_one]
      exact s.2
    have hxzv : H.mkW Fr.f xz = (π : E) • H.mkW Fr.f (πi • xz) := by
      refine Eq.trans ?_ (map_smul (H.mkW Fr.f) (π : E) (πi • xz))
      congr 1
      apply Subtype.ext
      show (xz : V) = (π : E) • (πi • (xz : V))
      rw [smul_smul, mul_comm, hinv, one_smul]
    have hu := hprim π (πi • xz) hvL hxzv
    exact hm.ne_top (hπ.trans (Ideal.span_singleton_eq_top.2 hu))
  have h1 : (1 : M.L.O) ∈ I := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y0, hy0L, hy0z⟩ := (hI 1).1 h1
  have hy0z' : H.h (Fr.f (Fin.last r)) (y0 : V) = 1 := hy0z

  obtain ⟨w, hw⟩ : ∃ w : V, w = ∑ a : Fin r, H.h (y0 : V) (Fr.es a) • Fr.f a.castSucc := ⟨_, rfl⟩
  have hwX : w ∈ H.X Fr.f := by
    rw [hw]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Fj_le_X Fr _ (e_mem Fr a))
  have hwp : w ∈ H.perp (H.X Fr.f) := X_le_perp Fr hwX
  have hsumL : ∀ (g : Fin r → V) (u : V) (s : Finset (Fin r)),
      H.h (∑ a ∈ s, g a) u = ∑ a ∈ s, H.h (g a) u := by
    intro g u s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.sum_empty, Finset.sum_empty]
      exact H.h_zero_left u
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  refine ⟨y0 - ⟨w, hwp⟩, ?_, ?_, ?_⟩
  · have hmk0 : H.mkW Fr.f ⟨w, hwp⟩ = 0 := by
      exact (Submodule.Quotient.mk_eq_zero _).2 hwX
    rw [map_sub, hmk0, sub_zero]
    exact hy0L
  · show H.h _ ((y0 : V) - w) = 1
    rw [h_sub_right, h_right H _ w, pairing_isotropicSpan_lastVector Fr w hwX, map_zero, sub_zero, hy0z']
  · intro b
    show H.h ((y0 : V) - w) (Fr.es b) = 0
    rw [h_sub_left, hw, hsumL]
    simp [H.h_smul_left, Fr.h_es]

end GlobalTheory.LocOver.InnerDual
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_measure_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  intro n ε a j W hW d E hcut hskew ν hν hinv ρ η hρ hρ8 hη
  set S := maxK ε ∩ flagM ε W with hS
  obtain ⟨t, ht, hsq⟩ := GlobalTheory.T.iwasawa_slab_squeezed_between_balls n ε S d E hcut ρ η hρ hρ8 hη
  obtain ⟨r0, hr0, hnear⟩ := GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection n ε a j W hW t ht
  have hmem : Set.Iio (min t r0) ∈ nhds (0 : ℝ) := Iio_mem_nhds (lt_min ht hr0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with r hr hr' u hu m hm k hk hball
  have hrpos : (0 : ℝ) < r := hr
  have hrlt : r < min t r0 := hr'
  have hrt : r < t := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrr0 : r < r0 := lt_of_lt_of_le hrlt (min_le_right _ _)

  have hb : nrm (uMat (u * m * k) - 1) ≤ r := hball
  obtain ⟨l0, hl0S, hl0⟩ := hnear u hu m hm k hk (le_trans hb hrr0.le)

  obtain ⟨l1, hl1S, hcrd, hmin⟩ := GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra n ε S d E hcut (fun x hx => hx.1) hskew k hk
  have hnrm : nrm (uMat (l1 * k) - 1) < t := lt_of_le_of_lt (hmin l0 hl0S) hl0
  have key := fun l (hl : l ∈ S) => hsq r hrpos hrt (l1 * k) hnrm hcrd l hl

  have hA : ν {l | l * k ∈ slab ε E ρ r} = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
    calc ν {l | l * k ∈ slab ε E ρ r}
        = (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by rw [hinv l1 hl1S]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
          (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
          congr 1
          ext l
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
  rw [hA]
  constructor
  · calc ν (hsBall ε (r / (1 + η)))
        ≤ ν (hsBall ε (r / (1 + η)) ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν (hsBall ε (r / (1 + η)) ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν (hsBall ε (r / (1 + η)) ∩ S) := by rw [hν, add_zero]
      _ ≤ ν {l | l * (l1 * k) ∈ slab ε E ρ r} :=
          measure_mono (fun l hl => (key l hl.2).1 hl.1)
  · calc ν {l | l * (l1 * k) ∈ slab ε E ρ r}
        ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) := by rw [hν, add_zero]
      _ ≤ ν (hsBall ε ((1 + η) * r)) :=
          measure_mono (fun l hl => (key l hl.2).2 hl.1)

end GlobalTheory.IwConst
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.count_rational_elements_bounded_distance : CountRat := by
  first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.local_models_unsplit_almost_all : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  first | exact @GlobalTheory.LocSplitFinite.split_finite | exact GlobalTheory.LocSplitFinite.split_finite | (intros; apply GlobalTheory.LocSplitFinite.split_finite <;> assumption)
end
