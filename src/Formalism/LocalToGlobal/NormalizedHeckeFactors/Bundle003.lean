module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle002
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.Gal

namespace Formalism.L2

section Points

variable {O X : Type} [CommRing O] [IsDomain O] [Fintype X]

def evPt (T : Subalgebra O (X → O)) (x : X) : T →ₐ[O] O :=
  (Pi.evalAlgHom O (fun _ : X => O) x).comp T.val

@[simp] theorem evPt_apply (T : Subalgebra O (X → O)) (x : X) (f : T) : evPt T x f = (f : X → O) x := rfl

theorem evPt_injective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Injective (evPt T) := by
  intro x y hxy
  by_contra hne
  obtain ⟨f, hf, hfxy⟩ := hsep x y hne
  exact hfxy (congrArg (fun φ : T →ₐ[O] O => φ ⟨f, hf⟩) hxy)

theorem exists_delta (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) (x : X) :
    ∃ P : T, (P : X → O) x ≠ 0 ∧ ∀ y, y ≠ x → (P : X → O) y = 0 := by
  classical
  have key : ∀ y, y ≠ x → ∃ g ∈ T, g x ≠ 0 ∧ g y = 0 := by
    intro y hy
    obtain ⟨f, hf, hne⟩ := hsep x y (Ne.symm hy)
    refine ⟨f - algebraMap O (X → O) (f y), T.sub_mem hf (T.algebraMap_mem _), ?_, ?_⟩
    · simpa [sub_eq_zero] using hne
    · simp
  choose g hgT hgx hgy using key
  let e : X → T := fun y => if hy : y = x then 1 else ⟨g y hy, hgT y hy⟩
  refine ⟨∏ y, e y, ?_, ?_⟩
  · simp only [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun y _ => ?_
    by_cases hy : y = x
    · simp [e, hy]
    · simp [e, hy, hgx y hy]
  · intro y hy
    simp only [SubmonoidClass.coe_finsetProd, Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (by simp [e, hy, hgy y hy])

theorem evPt_surjective (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : Function.Surjective (evPt T) := by
  classical
  intro φ
  choose P hPx hPy using exists_delta T hsep
  set N : O := ∏ y, ((P y : T) : X → O) y with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun y _ => hPx y
  let c : X → O := fun x => ∏ y ∈ Finset.univ.erase x, ((P y : T) : X → O) y
  have hsum : (∑ x, c x • P x : T) = algebraMap O T N := by
    apply Subtype.ext
    funext z
    have hR : ((algebraMap O T N : T) : X → O) z = N := by simp
    rw [hR]
    simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single z (fun x _ hxz => by rw [hPy x z (fun h => hxz h.symm), mul_zero])
      (fun h => absurd (Finset.mem_univ z) h)]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ z)
  have hφ : ∃ x, φ (P x) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h1 := congrArg φ hsum
    rw [AlgHom.commutes] at h1
    exact hN0 (by simpa [hcon] using h1.symm)
  obtain ⟨x0, hx0⟩ := hφ
  refine ⟨x0, AlgHom.ext fun g => ?_⟩
  have hmul : g * P x0 = ((g : X → O) x0) • P x0 := by
    apply Subtype.ext
    funext z
    by_cases hz : z = x0
    · subst hz
      simp
    · simp [hPy x0 z hz]
  have h2 := congrArg φ hmul
  rw [map_mul, map_smul, smul_eq_mul] at h2
  have h3 := mul_right_cancel₀ hx0 h2
  rw [evPt_apply]
  exact h3.symm

def ptsEquiv (T : Subalgebra O (X → O))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, (f : X → O) x ≠ (f : X → O) y) : X ≃ (T →ₐ[O] O) :=
  Equiv.ofBijective (evPt T) ⟨evPt_injective T hsep, evPt_surjective T hsep⟩

end Points

section Record

variable (D : D7)

def ptsNd (i : D.nd.Loc) : D.nd.X i ≃ (D.nd.T i →ₐ[D.nd.O i] D.nd.O i) :=
  ptsEquiv (D.nd.T i) (D.nd.T_sep i)

theorem zgoodSub : D.nd.ZgoodSub := fun i x hx =>
  (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1

theorem s0_eq (i : D.nd.Loc) : D.nd.s0 i = max 1 (D.host.QS.factorization (D.nd.l i)) := by
  by_cases h : D.nd.l i = 2
  · have h1 : 1 ≤ D.host.QS.factorization 2 :=
      (Nat.prime_two.dvd_iff_one_le_factorization D.host.QS_pos.ne').1
        ((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans D.host.tower_dvd)
    rw [D.nd.restNLevelExponent_of_two i h, h, max_eq_right h1]
  · exact D.nd.restNLevelExponent_of_odd i h

theorem mem_S_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) : v ∈ D.nd.S i ↔
    (v ∈ placesOver D.host.E (D.host.g 0) ∨ v ∈ placesOver D.host.E (D.host.g 1) ∨
      v ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
      v ∉ placesOver D.host.E (D.nd.l i) :=
  D.nd.S_def i v

theorem mem_Q_iff (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)) :
    v ∈ D.nd.Q i ↔ ∃ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), D.ntw.psiL i σ ≠ 1 :=
  (D.ntw.psiL_ram i v (D.nd.plOm.1 v) (D.nd.plOm.2 v)).symm

end Record

section Good

open Polynomial

end Good

section Tame

end Tame

def latRel {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Set (L.gen → O) :=
  {r | ∑ g : L.gen, φ (r g) • (g : V) = 0}

def latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V] (L : Rows.OLat O φ V) :
    Submodule O (L.gen → O) where
  carrier := latRel L
  zero_mem' := by simp [latRel]
  add_mem' := by
    intro a b ha hb
    simp only [latRel, Set.mem_ofPred_eq, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [latRel, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul] at ha ⊢
    rw [← Finset.smul_sum, ha, smul_zero]

@[simp] theorem mem_latRelSub {O : Type} [CommRing O] {φ : O →+* ℂ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : Rows.OLat O φ V) (r : L.gen → O) : r ∈ latRelSub L ↔ r ∈ latRel L := Iff.rfl

def plF (D : D7) (k : Fin 2) : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) :=
  {v | ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal}

theorem embK_OtoLL_mem (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    D.nd.embK i (D.what₂.OtoLL y) ∈ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range := by
  rw [← D.nd.embK_w i]
  by_cases h0 : D.what₂.OtoLL y = 0
  · rw [h0, AddValuation.map_zero]; exact le_top
  · rw [D.val_eq _ _ h0]
    have hint := D.O_int y
    set x : 𝓞 D.what₂.LL := ⟨D.what₂.OtoLL y, hint⟩
    have hx : (x : D.what₂.LL) = D.what₂.OtoLL y := rfl
    have hle := (D.plEq (D.nd.w i)).valuation_le_one (K := D.what₂.LL) x
    have hne : (D.plEq (D.nd.w i)).valuation D.what₂.LL (algebraMap (𝓞 D.what₂.LL) D.what₂.LL x) ≠ 0 := by
      simpa [hx] using h0
    unfold vAdd
    have : WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)) ≤ 0 := by
      have hne' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≠ 0 := by simpa [hx] using hne
      have hle' : (D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y) ≤ 1 := by simpa [hx] using hle
      have h2 : WithZero.exp (WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y))) ≤
          WithZero.exp (0 : ℤ) := by
        rw [WithZero.exp_log hne']; simpa using hle'
      exact WithZero.exp_le_exp.mp h2
    exact_mod_cast (by omega : (0:ℤ) ≤ -WithZero.log ((D.plEq (D.nd.w i)).valuation D.what₂.LL (D.what₂.OtoLL y)))

def fracRangeEquiv (O : Type) [CommRing O] [IsDomain O] :
    O ≃+* (algebraMap O (FractionRing O)).range :=
  RingEquiv.ofBijective (algebraMap O (FractionRing O)).rangeRestrict
    ⟨fun _ _ h => IsFractionRing.injective O (FractionRing O) (congrArg Subtype.val h),
     (algebraMap O (FractionRing O)).rangeRestrict_surjective⟩

def sOf (D : D7) (i : D.nd.Loc) : D.what₂.O →+* D.nd.O i :=
  (fracRangeEquiv (D.nd.O i)).symm.toRingHom.comp
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i))

theorem sOf_spec (D : D7) (i : D.nd.Loc) (y : D.what₂.O) :
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (sOf D i y) = D.nd.embK i (D.what₂.OtoLL y) := by
  have h := (fracRangeEquiv (D.nd.O i)).apply_symm_apply
    (((D.nd.embK i).comp D.what₂.OtoLL).codRestrict _ (embK_OtoLL_mem D i) y)
  exact congrArg Subtype.val h

structure NormalizedDataCompatibility (D : D7) where
  bj : ∀ i, (D.what₂.MjLat (D.nd.j i)).gen → D.nd.Bj i
  bj_span : ∀ i, Submodule.span (D.nd.O i) (Set.range (bj i)) = ⊤
  bj_rel : ∀ i (c : (D.what₂.MjLat (D.nd.j i)).gen → D.nd.O i), ∑ g, c g • bj i g = 0 ↔
    c ∈ Submodule.span (D.nd.O i) ((fun r => (sOf D i) ∘ r) '' latRel (D.what₂.MjLat (D.nd.j i)))

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions

namespace Formalism.L2

structure NormalizedHeckeDataPlaceholder (D : D7) : Type

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.N NumberField Polynomial

namespace Formalism.L2

open Formalism.L2.NT Formalism.L2.Host

variable (D : D7)

def KQbar (jE : D.host.E →+* Qb) : Fld := D.host.K.map jE.toRatAlgHom

def MrayC (jE : D.host.E →+* Qb) : Fld := rayField (KQbar D jE) (D.host.QS * D.host.q * D.host.d)

def ParC : Type :=
  {Sig : List (Part D.naut.CG) //
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r}

structure NormalizedTypesCompatibility (jE : D.host.E →+* Qb) where

  eM : D.ntypes.Mray ≃+* MrayC D jE
  eM_K : ∀ x : D.host.K, ((eM (algebraMap D.host.K D.ntypes.Mray x) : MrayC D jE) : Qb) = jE x

  tA : Fin 2 → ValuationSubring ℂ
  tκ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (tA k) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)
  teichC_def : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsTeich (tA k) (tκ k) (D.ntypes.teichC k)

  iota_loc : ∀ i : D.nd.Loc, haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime :=
      ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ (B : ValuationSubring ℂ) (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar (D.nd.w i))),
      (∀ y : D.nd.O i, ∃ h : D.naut.iotaQC i (D.naut.iotaQ i (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) y)) ∈ B,
        fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
          (κ (IsLocalRing.residue B ⟨_, h⟩)) = D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)) ∧
      ∀ k v x, D.ntypes.iota k v (D.nd.w i) x = redThrough B κ (D.ntypes.teichC k x)

  ζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ℕ → Formalism.CyclotomicNorms.Fbar (D.host.g k)
  ζ_gen : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsGenSys (ζ k)

  O : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (ζ k) (ζ_gen k))
  eSer_def : ∀ k f, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.ntypes.eSer k f = eSerO (O k) D.R.r f

  kv : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)

  tg_tame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (kv k v) (D.ntypes.tg k v) (ζ k)

  O_equiv : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant (O k)

  O_tw : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabTwLawO (O k)

  eP : D.ntypes.Par ≃ ParC D
  locPar_def : ∀ σ w, D.ntypes.locPar σ w = isoLoc D.nd D.naut (eP σ).1 w

variable {D}
variable {jE : D.host.E →+* Qb}

namespace NT

end NT

theorem eSer_zero_of_tie (T : NormalizedTypesCompatibility D jE) (k : Fin 2) (f : (ZMod (D.host.g k))[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = D.R.r ∧ f.coeff 0 ≠ 0)) : D.ntypes.eSer k f = 0 := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  rw [T.eSer_def]
  exact eSerO_eq_zero _ _ f hf


variable (D)

variable {D}

theorem lpDim_foldr {w : PlE D.host} {a : ℕ} {β : Type} (π : D.naut.CG a) (L : List β) (f : β → ℝ)
    (z : D.naut.LP w) :
    D.naut.lpDim (L.foldr (fun k acc => D.naut.lpSum (D.naut.lpTw (D.naut.locG π w) (f k)) acc) z) =
      L.length * a + D.naut.lpDim z := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [D.naut.lpDim_sum, D.naut.lpDim_tw, D.naut.locG_dim, ih]
    ring

theorem lpDim_spehLoc (p : Part D.naut.CG) (w : PlE D.host) :
    D.naut.lpDim (spehLoc D.nd D.naut p w) = p.a * p.d := by
  unfold spehLoc
  have h := lpDim_foldr (D := D) p.π (do let a ← List.range p.d; pure (a : ℝ))
    (fun k : ℝ => ((p.d : ℝ) - 1) / 2 - k) (D.naut.lpZero w)
  rw [h, D.naut.lpDim_zero, add_zero, mul_comm]
  congr 1
  simp

theorem lpDim_isoLoc (Sig : List (Part D.naut.CG)) (w : PlE D.host) :
    D.naut.lpDim (isoLoc D.nd D.naut Sig w) = rankIso D.nd D.naut Sig := by
  induction Sig with
  | nil => simp [isoLoc, rankIso, D.naut.lpDim_zero]
  | cons p Sig ih =>
    unfold isoLoc at ih ⊢
    unfold rankIso at ih ⊢
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [D.naut.lpDim_sum, lpDim_spehLoc, ih]

section Deg

variable {G : Type} [Group G] {g : ℕ} (f₀ : (ZMod g)[X])

end Deg

end Formalism.L2
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace Formalism.L2.NC

def iotaC (D : D7) (i : D.nd.Loc) : D.nd.O i →+* ℂ :=
  ((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).comp (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

def complexEmbeddingRestrictedToSubfield (D : D7) : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom

structure NChiData (D : D7) where

  mu0 : ℕ → HC D.host.E

  etaT : HC D.host.E

  del : D.ntw.Tw → HC D.host.E

  psi : D.nd.Loc → HC D.host.E

  chiI : ∀ s, D.ntw.abelian₂ s → HC D.host.E

  embO : ∀ s, Bool → ↥D.LL0 →+* FractionRing (D.ntw.O s)

def NChiData.firstHeckeCharacter {D : D7} (K : NChiData D) (s : D.ntw.Tw) (j : ℕ) : HC D.host.E :=
  K.mu0 j * K.del s * (K.etaT)⁻¹

def NChiData.lamH {D : D7} (K : NChiData D) (s : D.ntw.Tw) (lam : D.ntw.abelian₂ s) : HC D.host.E :=
  K.mu0 (D.ntw.jL s lam) * K.del s * (K.chiI s lam)⁻¹

structure NormalizedCharacterCompatibility (D : D7) (K : NChiData D) : Prop where

  psi : ∀ a, ReadC D.nd.plOm.1 (D.ntw.psiL a) (iotaC D a) (K.psi a) 0

  del_fix : ∀ s s', D.ntw.pD s = D.ntw.pD s' → K.del s = K.del s'

  delta : ∀ s, Read D.nd.plOm.1 (D.ntw.delta s) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (D.ntw.emb0 s)
    (complexEmbeddingRestrictedToSubfield D) (K.del s) 0

  chi1 : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → Read D.nd.plOm.1 (D.ntw.chi1 s j b) (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)))
    (if b then D.ntw.emb0 s else D.ntw.emb0b s) (complexEmbeddingRestrictedToSubfield D) (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))

  ringSpec_sidedEmbedding_fixedField : ∀ s (b : Bool) (x : ↥D.LL0) (y : D.ntw.O0 s),
    algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s)) y = (if b then D.ntw.emb0 s else D.ntw.emb0b s) x →
    K.embO s b x = algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)) (algebraMap (D.ntw.O0 s) (D.ntw.O s) y)

  etaT_unr : ∀ P, K.etaT.Unr P

  etaT_inf : ∀ g : D.R.Psi, K.etaT.IsUnitArg (D.host.emb (g : D.R.GG))

  lamG : ∀ s lam, Read D.nd.plOm.1 (D.ntw.lamG s lam) (algebraMap (D.ntw.O s) (FractionRing (D.ntw.O s)))
    (K.embO s (D.ntw.sideL s lam)) (complexEmbeddingRestrictedToSubfield D) (K.lamH s lam) 0

section rcg

variable (D : D7)

end rcg

theorem frob_exists (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ∃ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ :=
  exists_isFrob (D.nd.plOm.2 P)

end Formalism.L2.NC
end
end
