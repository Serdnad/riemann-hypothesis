module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle005
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle007
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
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div2

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_div_mem {m : ℤ} {e : ℤ → V} (he : LB m e) (D : Submodule LL V) (hD : ∀ k, e k ∈ D)
    (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e ∧ ∀ k, d k ∈ D := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_, smulS_mem hLB' D (fun k => hD _) _⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_linMap {V' : Type} [AddCommGroup V'] [Module LL V'] (Φ : V →ₗ[LL] V') {m : ℤ}
    {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) :
    Φ (smulS g f k) = smulS g (fun j => Φ (f j)) k := by
  have hf' : LB m (fun j => Φ (f j)) := fun j hj => by simp [hf j hj]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N :=
    ⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩

  rw [smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, map_sum]
  simp [map_smul]

end Div2

section Rules

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem levN_smulS (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = smulS (W.lev i ζ a) (W.levN T i ζ x) := by
  funext k
  rw [W.levN_smul]
  rfl

theorem isExp_unique (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d d' : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d)
    (hd' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d') : d = d' := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  obtain ⟨⟨m', hm'⟩, a', ha', hla', he'⟩ := hd'
  have hdl : LB (min m m') d := fun k hk => hm k (by omega)
  have hdl' : LB (min m m') d' := fun k hk => hm' k (by omega)
  have hlev : W.levN T i ζ ⟨a • x, ha⟩ = smulS (W.lev i ζ a) d := funext he
  have hlev' : W.levN T i ζ ⟨a' • x, ha'⟩ = smulS (W.lev i ζ a') d' := funext he'
  have e : a' • (⟨a • x, ha⟩ : ↥(W.N T)) = a • (⟨a' • x, ha'⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_smul, smul_smul, mul_comm])
  have h := congrArg (W.levN T i ζ) e
  rw [levN_smulS, levN_smulS, hlev, hlev', ← smulS_mul hdl, ← smulS_mul hdl', mul_comm] at h
  exact smulS_inj hdl hdl' _ (mul_ne_zero hla hla') h

theorem expRules_of (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hN : GamN W) (hA' : GamA W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := by
  intro hA T hT i ζ hζ
  have hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := fun x k => by
    have := (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 x k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero] at this
    exact (Submodule.mem_inf.1 this).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x a ha hla
    obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d, hd, hde⟩ := smulS_div (m := m) hm _ hla
    have hE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d :=
      ⟨⟨m', hd⟩, a, ha, hla, fun k => (congrFun hde k).symm⟩
    exact ⟨d, hE, fun d' hd' => isExp_unique W T i ζ hd' hE⟩
  ·
    intro x d _ hx k
    obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hx
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d₀, hd₀, hde₀, hmem⟩ := smulS_div_mem (m := m₀) hm₀ (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
      (fun k => hLv _ k) _ hla
    have hE₀ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d₀ :=
      ⟨⟨m', hd₀⟩, a, ha, hla, fun k => (congrFun hde₀ k).symm⟩
    rw [isExp_unique W T i ζ ⟨⟨m, hm⟩, a, ha, hla, he⟩ hE₀]
    exact hmem k
  ·
    rintro x y d e ⟨⟨m, hm⟩, a, ha, hla, hd⟩ ⟨⟨m', hm'⟩, b, hb, hlb, he⟩
    have hdl : LB (min m m') d := fun k hk => hm k (by omega)
    have hel : LB (min m m') e := fun k hk => hm' k (by omega)
    have hmem : (a * b) • (x + y) ∈ W.N T := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
      exact (W.N T).add_mem ((W.N T).smul_mem b ha) ((W.N T).smul_mem a hb)
    refine ⟨⟨min m m', LB_add hdl hel⟩, a * b, hmem, by rw [map_mul]; exact mul_ne_zero hla hlb,
      fun k => ?_⟩
    have e1 : (⟨(a * b) • (x + y), hmem⟩ : ↥(W.N T)) =
        b • (⟨a • x, ha⟩ : ↥(W.N T)) + a • (⟨b • y, hb⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [Submodule.coe_add, SetLike.val_smul]
        rw [smul_add, smul_smul, smul_smul, mul_comm b a])
    rw [e1, map_add (f := _), Pi.add_apply, levN_smulS, levN_smulS, funext hd, funext he]
    show smulS (W.lev i ζ b) (smulS (W.lev i ζ a) d) k + smulS (W.lev i ζ a) (smulS (W.lev i ζ b) e) k =
      smulS (W.lev i ζ (a * b)) (d + e) k
    rw [map_mul, smulS_add hdl hel, ← smulS_mul hdl, ← smulS_mul hel, mul_comm (W.lev i ζ b)]
    rfl
  ·
    rintro c x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (c • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_of_tower_mem c ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (c • x), hmem⟩ : ↥(W.N T)) =
        (algebraMap O (LetA O n) c) • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [SetLike.val_smul]
        rw [algebraMap_smul, smul_comm])
    rw [e1, levN_smulS, funext hd, AlgHom.commutes, PowerSeries.algebraMap_apply]
    show smulS (PowerSeries.C (algebraMap O LL c)) (smulS (W.lev i ζ a) d) k =
      smulS (W.lev i ζ a) (fun k => algebraMap O LL c • d k) k
    rw [smulS_C (LB_smulS hm _)]
    have e2 : (fun k => algebraMap O LL c • d k) = algebraMap O LL c • d := rfl
    rw [e2, smulS_smul hm]
  ·
    rintro a' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (a' • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_mem a' ha
    refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
    rw [e1, levN_smulS, funext hd]
    show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
    rw [smulS_comm hm]
  ·
    rintro x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0 :=
      ((Units.isUnit (W.χΓ W.gam)).map (algebraMap O LL)).ne_zero
    have hγN' : W.γ T (a • x) ∈ W.N T := W.N_Γ T W.gam _ ha
    have hmem : W.γA W.gam a • W.γ T x ∈ W.N T := by
      have h := hγN'
      change W.γD T W.gam (a • x) ∈ W.N T at h
      rw [RL.γD_smulA] at h
      exact h
    refine ⟨⟨m, LB_resc hm _⟩, W.γA W.gam a, hmem, ?_, fun k => ?_⟩
    · rw [hA' i ζ hζ a]
      intro h0
      exact hla (PowerSeries.rescale_injective hχ (h0.trans (map_zero _).symm))
    · have e1 : (⟨W.γA W.gam a • W.γ T x, hmem⟩ : ↥(W.N T)) =
          ⟨W.γ T ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), hγN'⟩ :=
        Subtype.ext (RL.γD_smulA W T W.gam a x).symm
      rw [e1, hN T hT i ζ hζ ⟨a • x, ha⟩ hγN' k, funext hd, hA' i ζ hζ a]
      show algebraMap O LL (W.χΓ W.gam : O) ^ k • smulS (W.lev i ζ a) d k =
        smulS (PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ a))
          (resc (algebraMap O LL (W.χΓ W.gam : O)) d) k
      rw [smulS_rescale hm _ hχ]
      rfl
  ·
    rintro T' F hT' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • W.map F x ∈ W.N T' := by
      rw [← RL.map_smulA]; exact W.map_N F hT hT' _ ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • W.map F x, hmem⟩ : ↥(W.N T')) =
        ⟨W.map F ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), by rw [← RL.map_smulA] at hmem; exact hmem⟩ :=
      Subtype.ext (RL.map_smulA W F a x).symm
    rw [e1, W.levN_map F hT hT' i ζ, hd]
    exact smulS_linMap _ hm _ k

end Rules

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

section Lin

variable {O : Type} [CommRing O] {A M : Type} [AddCommGroup A] [Module O A] [AddCommGroup M]
  [Module O M]

theorem linLift (K : Submodule O M) (R : A → M → Prop) (hex : ∀ a, ∃ x, R a x)
    (hadd : ∀ a a' x x', R a x → R a' x' → R (a + a') (x + x'))
    (hsmul : ∀ (o : O) a x, R a x → R (o • a) (o • x))
    (huniq : ∀ a x x', R a x → R a x' → x - x' ∈ K) :
    ∃ ψ : A →ₗ[O] M ⧸ K, ∀ a, ∃ x, R a x ∧ ψ a = K.mkQ x := by
  choose g hg using hex
  refine ⟨{ toFun := fun a => K.mkQ (g a), map_add' := ?_, map_smul' := ?_ }, fun a => ⟨g a, hg a, rfl⟩⟩
  · intro a a'
    rw [← map_add (f := _)]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (a + a')) (hadd _ _ _ _ (hg a) (hg a')))
  · intro o a
    rw [RingHom.id_apply, ← map_smul]
    exact (Submodule.Quotient.eq K).2 (huniq _ _ _ (hg (o • a)) (hsmul o _ _ (hg a)))

end Lin

section bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem pchain_DN' (i : ZMod n) (k : ℕ) {m : ℕ} {cc : ℝ} {FF : Type} [AddCommGroup FF]
    [Module O FF] (K : Submodule O ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) (s : Finset (W.DD T))
    (hs : s.card ≤ m) (hsN : (↑s : Set (W.DD T)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) (L kO : ℕ)
    (hL : Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸
      (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype) ≤ (L : ℕ∞))
    (hkO : lenOl PD (O := O) = kO) (hLc : (L : ℝ) ≤ cc * kO) (A : Submodule O FF)
    (ψ : ↥A →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) :
    Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc A
      (kerSub A ψ (((Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype).map K.mkQ)) 1 1 := by
  set X := (Xd W T i k).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hXdef
  set Y := (Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T))).comap
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype with hYdef
  have hXY : X ≤ Y := Submodule.comap_mono le_sup_left
  have hlen : Module.length O ((↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K) ⧸ Y.map K.mkQ) ≤ (L : ℕ∞) := by
    rw [(Submodule.quotientQuotientEquivQuotientSup K Y).length_eq]
    refine le_trans ?_ hL
    exact Module.length_le_of_surjective (Submodule.mapQ Y (K ⊔ Y) LinearMap.id
      (fun y hy => Submodule.mem_sup_right (by simpa using hy)))
      (fun z => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
        exact ⟨Submodule.Quotient.mk x, rfl⟩)
  have h1 := pstep_len (m := m) (c := cc) A ψ (Y.map K.mkQ) L kO hlen hkO hLc
  set A₁ := kerSub A ψ (Y.map K.mkQ) with hA₁def
  have hA₁ : A₁ ≤ A := kerSub_le A ψ _
  set ψ₁ : ↥A₁ →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) ⧸ K := ψ.comp (Submodule.inclusion hA₁)
  set sN : Finset ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i) := s.subtype (· ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)
  set s' := sN.image K.mkQ
  have hcard : s'.card ≤ m := by
    refine Finset.card_image_le.trans (le_trans ?_ hs)
    rw [Finset.card_subtype]
    exact Finset.card_filter_le _ _
  have hspan : Submodule.span O (↑s : Set (W.DD T)) =
      (Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i))).map
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).subtype := by
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · intro hy
      exact ⟨⟨y, hsN hy⟩, Finset.mem_subtype.2 hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact Finset.mem_subtype.1 hz
  have hY : Y ≤ X ⊔ Submodule.span O (↑sN : Set ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i)) := by
    intro z hz
    have hz' : (z : W.DD T) ∈ Xd W T i k ⊔ Submodule.span O (↑s : Set (W.DD T)) := hz
    obtain ⟨x, hx, t, ht, hxt⟩ := Submodule.mem_sup.1 hz'
    rw [hspan] at ht
    obtain ⟨t', ht', rfl⟩ := Submodule.mem_map.1 ht
    have hxN : x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i := by
      have e : x = (z : W.DD T) - (t' : W.DD T) := by rw [← hxt]; simp
      rw [e]; exact (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T i).sub_mem z.2 t'.2
    refine Submodule.mem_sup.2 ⟨⟨x, hxN⟩, hx, t', ht', Subtype.ext ?_⟩
    simpa using hxt
  have hgen : ∀ a, ψ₁ a ∈ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
    intro a
    have ha : ψ ⟨(a : FF), hA₁ a.2⟩ ∈ Y.map K.mkQ := (mem_kerSub_coe A ψ _ ⟨a, hA₁ a.2⟩).1 a.2
    have hle : Y.map K.mkQ ≤ X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
      calc Y.map K.mkQ ≤ (X ⊔ Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_mono hY
        _ = X.map K.mkQ ⊔ (Submodule.span O (↑sN : Set _)).map K.mkQ := Submodule.map_sup _ _ _
        _ = X.map K.mkQ ⊔ Submodule.span O (↑s' : Set _) := by
          rw [Submodule.map_span, Finset.coe_image]
    exact hle ha
  have h2 := pstep_gen (lenO := lenOl PD (O := O)) (m := m) (c := cc) A₁ ψ₁ (X.map K.mkQ) s' hcard hgen
  have heq : kerSub A₁ ψ₁ (X.map K.mkQ) = kerSub A ψ (X.map K.mkQ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A₁ ψ₁ _ x).1 hx
      exact (mem_kerSub A ψ _ x).2 ⟨hA₁ hx1, hx2⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := (mem_kerSub A ψ _ x).1 hx
      have hx1' : x ∈ A₁ := (mem_kerSub A ψ _ x).2 ⟨hx1, Submodule.map_mono hXY hx2⟩
      exact (mem_kerSub A₁ ψ₁ _ x).2 ⟨hx1', hx2⟩
  rw [heq] at h2
  exact (pchain_of_len h1).trans (pchain_of_gen h2)

end bigCellDetWeightedEnergyIntegral

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
