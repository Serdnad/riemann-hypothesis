module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PairValPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocUnramB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.WeightConstB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle023
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle007
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeGluingRadicals
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
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.PCount

namespace IntegralGeneration

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_smul_right (x y : V) (c : E) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem fst_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).1 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).1 := by
    have := hx.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem snd_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).2 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).2 := by
    have := hx.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem mem_R_of_split {g : Loc.SplitG M.L} (hM : M.split = some g) (x : E) :
    x ∈ M.R ↔ g.e x ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[F]) (g.q : F) := by
  obtain ⟨L, s, mu⟩ := M
  simp only at hM g ⊢
  subst hM
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x

theorem e_alg (g : Loc.SplitG M.L) (c : F) : g.e (algebraMap F E c) = (c, c) := by
  rw [g.e.commutes]; rfl

theorem zzplus_int {r : ℕ} {t : Loc.Term V M r} (ht : H.IsGeneric t) (a b : Fin (r + 1)) :
    H.ZZplus t a b ∈ M.R := by
  obtain ⟨⟨hSD, hF, hF', -, -, hG⟩, hP⟩ := ht
  have hfL : ∀ a, t.f a ∈ t.abelian₂ := hF.1.1
  have hfL' : ∀ a, t.f' a ∈ t.abelian₂ := hF'.1.1
  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := fun x hx y hy => (hSD.2.2 x).1 hx y hy
  have hff : ∀ a b : Fin (r + 1), H.h (t.f b) (t.f a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF.2.2.1
    · exact hF.2.1 b a (not_and_or.mp hc).symm
  have hff' : ∀ a b : Fin (r + 1), H.h (t.f' b) (t.f' a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T' else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF'.2.2.1
    · exact hF'.2.1 b a (not_and_or.mp hc).symm
  rcases hM : M.split with _ | g
  ·
    have hR : M.R = M.L.O := by simp only [Loc.Model.R, hM]
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [hR]
    exact hint _ (hfL' b) _ (hfL a)
  ·
    obtain ⟨-, ⟨c, hc⟩, -⟩ := hG g hM
    have hq : (g.q : F) ≠ 0 := by
      intro h; apply g.q_irr.ne_zero; exact_mod_cast h
    set q : F := (g.q : F) with hq_def
    set k : E := algebraMap F E q with hk
    set n : Fin (r + 1) → V := fun a => algebraMap F E q⁻¹ • (t.f' a - t.f a) with hn_def
    have hnL : ∀ a, n a ∈ t.abelian₂ := fun a => by
      have := hP.1 (Sum.inr a)
      simpa only [Loc.HermSp.MMfam, hM, Sum.elim_inr] using this
    have hf' : ∀ a, t.f' a = t.f a + k • n a := fun a => by
      simp only [hn_def, hk, smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
      abel
    have hcjk : M.L.cj k = k := M.L.cj.commutes q
    have hek : g.e k = (q, q) := e_alg g q

    have E1 : H.h (t.f' b) (t.f a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) := by
      rw [hf' b, H.h_add_left, H.h_smul_left]
    have E2 : H.h (t.f' a) (t.f b) = H.h (t.f a) (t.f b) + k * H.h (n a) (t.f b) := by
      rw [hf' a, H.h_add_left, H.h_smul_left]
    have E3 : H.h (t.f' b) (t.f' a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) +
        k * H.h (t.f b) (n a) + k * k * H.h (n b) (n a) := by
      rw [hf' b, hf' a]
      simp only [H.h_add_left, H.h_smul_left, h_add_right, h_smul_right, hcjk]
      ring
    have hswap : (g.e (H.h (n a) (t.f b))).2 = (g.e (H.h (t.f b) (n a))).1 := by
      rw [H.h_herm (t.f b) (n a), g.e_cj]; rfl
    have hA := fst_mem (g := g) (hint _ (hnL b) _ (hfL a))
    have hB := snd_mem (g := g) (hint _ (hnL a) _ (hfL b))
    have hC := fst_mem (g := g) (hint _ (hnL b) _ (hnL a))
    have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    have F1 : (g.e (H.h (t.f' b) (t.f a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 := by
      rw [E1]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    have F2 : (g.e (H.h (t.f' a) (t.f b))).2 = (g.e (H.h (t.f a) (t.f b))).2 + q * (g.e (H.h (n a) (t.f b))).2 := by
      rw [E2]; simp only [map_add (f := _), map_mul, hek, Prod.snd_add, Prod.snd_mul]
    have F3 : (g.e (H.h (t.f' b) (t.f' a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 +
        q * (g.e (H.h (n a) (t.f b))).2 + q * q * (g.e (H.h (n b) (n a))).1 := by
      rw [E3, hswap]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    generalize (g.e (H.h (n b) (t.f a))).1 = A at hA F1 F3
    generalize (g.e (H.h (n a) (t.f b))).2 = B at hB F2 F3
    generalize (g.e (H.h (n b) (n a))).1 = C at hC F3
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [mem_R_of_split hM]
    by_cases hcn : a = Fin.last r ∧ b = Fin.last r
    · obtain ⟨rfl, rfl⟩ := hcn
      have h1 := hff (Fin.last r) (Fin.last r)
      have h1' := hff' (Fin.last r) (Fin.last r)
      simp only [and_self, if_true] at h1 h1' ⊢
      rw [h1, map_neg, e_alg] at F1 F2 F3
      rw [h1', map_neg, e_alg] at F3
      simp only [Prod.fst_neg, Prod.snd_neg] at F1 F2 F3
      rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · simp only [Prod.fst_sub]
        have : (-t.T + q * A) / q - -t.T / q = A := by linear_combination A * hqq
        rw [this]; exact hA
      · simp only [Prod.snd_sub]
        have : -((-t.T + q * B) / q) - t.T' / q = q * c - B := by
          linear_combination q⁻¹ * hc + (q * c - B) * hqq
        rw [this]; exact sub_mem (mul_mem g.q.2 c.2) hB
      · simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq
    · have h1 := hff a b
      have h1' := hff' a b
      have h2 : H.h (t.f a) (t.f b) = 0 := by
        have := hff b a
        rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hcn ⟨rfl, rfl⟩)] at this
        exact this
      rw [if_neg hcn] at h1 h1' ⊢
      rw [h1, map_zero] at F1 F3
      rw [h2, map_zero] at F2
      rw [h1', map_zero] at F3
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at F1 F2 F3
      rw [sub_zero, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · have : q * A / q = A := by linear_combination A * hqq
        simp only; rw [this]; exact hA
      · have : -(q * B / q) = -B := by linear_combination (-B) * hqq
        simp only; rw [this]; exact neg_mem hB
      · simp only
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq

end IntegralGeneration

variable {D : Formalism.BasicNotions.D7}

theorem intGenP_holds (Zd : LocDat D) : IntGenP Zd :=
  fun p _ ht a b => IntegralGeneration.zzplus_int (locH Zd p) ht a b

end Formalism.L2.SG.Pf.PCount
end
end

section

noncomputable section

namespace Formalism.L2.SG.Pf.FibPart

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB Formalism.L2.SG.Pf.PCount
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def RepIn (γ : TermDef.Term D u u' F0 what₂) (Z : PairVal.MatR D) : Prop :=
  ∃ F' ∈ CntLocal.EZ (D := D) ((Tu D u' : ℕ) : D.host.E) F0 γ.lam Z,
    Rep γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') γ.cls F'

def Pre : Prop :=
  (∀ p, Agree δ M p) ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] ∧ PrimeHyp D u (Tu D u') ∧
    PairVal.NormRepExists D u u' F0 what₂ ∧ IsRowReps D F0 what₂ ∧ EligRel u u' F0 what₂

def TupFun : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z → locT M δ γ = tupZ M δ u u' Z

def RepAtTup : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)),
    Gpt (D.mem u).A.T (D.mem u').A.T w ≠ 0 → ∀ Z : PairVal.MatR D, AtMat w Z → EligAt γ w →
      locT M δ γ = tupZ M δ u u' Z → RepIn u u' F0 what₂ γ Z

def OrbZT : Prop :=
  Pre M δ u u' F0 what₂ → ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (Z : PairVal.MatR D),
    EligAt γ w → AtMat w Z → RepIn u u' F0 what₂ γ Z →
      (PairVal.orbT D u u' F0 what₂ γ (zT γ)).encard = (PairVal.orbT D u u' F0 what₂ γ Z).encard

end Steps

end Formalism.L2.SG.Pf.FibPart
end
end

section

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.LocUnramB

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups MeasureTheory Formalism.L2.SG.Pf.AtPt
open Formalism.L2.SG.LsDatumB Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Restr2

variable {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
  {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem thRestricted_of (hA : ∀ p, Agree δ M p) (hrows : IsRowReps D F0 what₂)
    (hN : PairVal.NormRepExists D u u' F0 what₂) (hRel : PCount.EligRel u u' F0 what₂) :
    ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) := by
  intro γ w h
  have hZ : PCount.AtMat w (zT γ) := PCount.atMat_zT hN hrows h (hRel γ w h)

  have hpt : ptT γ = w := by
    have h0 := h
    obtain ⟨⟨hgen, -⟩, hat⟩ := h
    obtain ⟨y, hy⟩ := hN γ w hat (hRel γ w h0) hgen
    have hex : ∃ x : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
        PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ x.1 x.2.1 x.2.2.1 x.2.2.2 := ⟨(w, y), hy⟩
    have hn : nrep γ = some hex.choose := dif_pos hex
    obtain ⟨hRep, -, hL, hU, e⟩ := hex.choose_spec
    obtain ⟨F₁, hR₁, -, hc₁⟩ := hat
    have hw : w = hex.choose.1 := pt_eq_of_cells cell_point_uniqueness (Formalism.L2.SG.Closed.TermFun_holds D u u') hrows γ
      hR₁ hRep hc₁ ⟨_, _, hL, hU, e⟩
    unfold ptT
    rw [hn]
    exact hw.symm
  have hfin := PCount.tupZ_restr hA u u' hZ
    ((LocModel.good_cofinite δ M hA ∅).mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)
    (fun x => LocModel.LM.iotaIntegral_almost_all D x)
  have hall := LocModel.good_cofinite δ M hA (w.1.map Prod.fst).toFinset
  rw [Filter.eventually_cofinite] at hall
  refine (hfin.union hall).subset fun p hp => ?_
  by_contra hq
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hq
  obtain ⟨htup, hg⟩ := hq
  have hg' : Good δ M w p := hg
  apply hp
  show thL M δ (D.mem u).A.T (D.mem u').A.T p (ptT γ) (CntLocal.ZZP (M := M) δ u u' p (zT γ)) = _
  rw [hpt]
  have hmem : CntLocal.ZZP (M := M) δ u u' p (zT γ) * LsDatumB.sgnP p ∈ x0L M δ (D.mem u).A.T (D.mem u').A.T p w := by
    rw [← htup]
    exact ⟨1, 1, one_intLow p, one_intUp p, by rw [Matrix.one_mul, Matrix.mul_one]⟩
  obtain ⟨l, ρ, hl, hρ, he⟩ := hmem
  have hZZ : CntLocal.ZZP (M := M) δ u u' p (zT γ) =
      l * modMat δ (D.mem u).A.T (D.mem u').A.T p w * ρ * LsDatumB.sgnP p := by
    rw [← he, Matrix.mul_assoc, permSign_mul_self₂, Matrix.mul_one]
  have e2 : CntLocal.ZZP (M := M) δ u u' p (zT γ) + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := by
    rw [hZZ, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, loU_corner p _ ⟨hl.1, hl.2.1⟩ ⟨hρ.1, hρ.2.1⟩,
      corner_sgn]
  unfold thL
  apply clsOf_triv
  have e3 : (CntLocal.ZZP (M := M) δ u u' p (zT γ) + Matrix.of fun a b =>
      if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then cornerSh δ (D.mem u).A.T (D.mem u').A.T p w else 0) =
      l * (modMat δ (D.mem u).A.T (D.mem u').A.T p w + cornerM p (cornerSh δ (D.mem u).A.T (D.mem u').A.T p w)) *
        ρ * LsDatumB.sgnP p := e2
  rw [e3]
  refine isGL_mul _ (isGL_mul _ (isGL_mul _ (isGL_of_det_one _ hl.2.2 (det_loU ⟨hl.1, hl.2.1⟩))
    (shift_isGL _ _ w p (hA p) hg')) (isGL_of_det_one _ hρ.2.2 (det_upU ⟨hρ.1, hρ.2.1⟩))) (isGL_sgn p)

end Restr2

end Formalism.L2.SG.Pf.LocUnramB

namespace Formalism.L2.SG.Pf

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut

theorem thRestricted_holds_of {D : Formalism.BasicNotions.D7} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    (hA : ∀ p, Agree δ M p) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (Formalism.L2.SG.CntLocal.Tn u)}
    {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hrows : IsRowReps D F0 what₂) (hN : Formalism.L2.SG.PairVal.NormRepExists D u u' F0 what₂)
    (hRel : PCount.EligRel u u' F0 what₂) :
    Formalism.L2.SG.LsDatumB.ThRestricted M δ u u' F0 what₂ (LocModel.thTriv M) :=
  LocUnramB.thRestricted_of hA hrows hN hRel

end Formalism.L2.SG.Pf
end
end

section

noncomputable section

namespace Formalism.L2.SG.WConst

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pos

variable {D : D7}

theorem gPoint_eq_gval {T T' : ℕ} (F : LFlag (D.sp.Y 0) D.R.rS (T : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T' : D.host.E))
    (w : Point D.host.E (D.R.rS + 1)) (hc : IsInCell (Formalism.MainNotions.S.ZhatOM (ZhatL F F')) w) :
    Gpt T T' w = Gval F F' := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hc
  have hL' : IsLo L := ⟨fun a => (hL a a).2 rfl, fun a b hab => (hL a b).1 hab⟩
  have hU' : IsUp U := ⟨fun a => (hU a a).2 rfl, fun a b hab => (hU b a).1 hab⟩
  have hS : Formalism.MainNotions.S.ZhatOM (ZhatL F F') = ZhatL F F' * Sg D.host.E D.R.rS := by
    ext a b
    simp [Formalism.MainNotions.S.ZhatOM, Sg, mul_diagonal, mul_comm]
  have key : ∀ l (hl : l ≤ D.R.rS + 1), leadMinorE (ZhatL F F') l * epsL (D := D) D.R.rS l hl = Dmin w l := by
    intro l hl
    rw [← leadMinor_Sg, ← hS, hZ, leadMinor_LMU hL' hU', dmin_eq']
  have n1 := norm_eq_of _ _ _ (key (D.R.rS + 1) le_rfl) (epsL_sq _ _) (star_epsL _ _)
  have n2 := norm_eq_of _ _ _ (key D.R.rS (Nat.le_succ _)) (epsL_sq _ _) (star_epsL _ _)
  simp only [Gval, Gflag, Gpt, conjF_star]
  unfold Formalism.MainNotions.S.Dl
  rw [n1, n2]

theorem atPt_totPos {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (t : Formalism.L2.SG.TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)) (h : t.atPt w) :
    TotPos (Gpt (D.mem u).A.T (D.mem u').A.T w) := by
  obtain ⟨F', ⟨hP, -⟩, hG, hc⟩ := h
  have e := gPoint_eq_gval (T := Tu D u) (T' := Tu D u') (lf D F0) F' w hc
  intro τ
  change 0 < (D.host.emb (D.eTau τ) (Gpt (Tu D u) (Tu D u') w)).re
  rw [e]
  exact (Formalism.MainNotions.LatticeGluingRadicals.b_G_pos (Formalism.MainNotions.LatticeGluingRadicals.p_starConj D) (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) (lf D F0) F' rfl
    hP.1.2 hG (Formalism.MainNotions.LatticeGluingRadicals.p_posX D _ (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u) _) _).1

end Pos

section Use

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem eligTotPos_holds : EligTotPos X Y u u' := fun t w _ h => atPt_totPos t w h

theorem kapN_pos : 0 < Formalism.L2.SG.MassDataConc.kapN D := by
  unfold Formalism.L2.SG.MassDataConc.kapN
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero _))) _
  have hg : 0 < ((Formalism.MainNotions.S.Lat.gS D : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  exact mul_pos (pow_pos hr _) (inv_pos.mpr (pow_pos hg _))

theorem weightBound_holds {nc : ℝ} (hnc : 0 < nc) : Formalism.L2.SG.RowsAbsX.WeightBound X Y u u' nc := by
  refine ⟨Real.sqrt (Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc)), fun p w hp hreal ht => ?_⟩
  obtain ⟨t, -, hat⟩ := ht
  have hT := atPt_totPos t w hat
  rw [nW_eq X u u' p w hp hreal hT hnc]
  have hK : 0 ≤ Formalism.L2.SG.MassDataConc.ngFac D / (Formalism.L2.SG.MassDataConc.kapN D * nc) := by
    refine div_nonneg ?_ (mul_pos kapN_pos hnc).le
    unfold Formalism.L2.SG.MassDataConc.ngFac
    exact pow_nonneg (Real.sqrt_nonneg _) _
  have hn0 : 0 ≤ n0 nc (D.mem u).A.T (D.mem u').A.T w := by
    unfold n0
    exact mul_nonneg hnc.le (pow_nonneg (Real.sqrt_nonneg _) _)
  rw [Real.sqrt_mul hK, Real.sqrt_mul hn0, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

end Use

end Formalism.L2.SG.WConst
end
end
