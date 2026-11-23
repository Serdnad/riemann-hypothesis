module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle010
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle010
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem lc_of_ker {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem res_dual (O : Type) [CommRing O] [IsLocalRing O] [IsCO O (DualNumber (ResidueField O))]
    (x : DualNumber (ResidueField O)) : res O (DualNumber (ResidueField O)) x = x.fst := by
  obtain ⟨a, ha⟩ := residue_surjective x.fst
  have h1 : x - algebraMap O _ a ∈ maximalIdeal (DualNumber (ResidueField O)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not,
      TrivSqZeroExt.fst_sub, ← ha]
    exact sub_self _
  have h2 := (res_eq_zero_iff O _ _).2 h1
  rw [map_sub, AlgHom.commutes, sub_eq_zero] at h2
  rw [h2, ← ha]
  rfl

private theorem of_unique {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C : Type}
    [CommRing C] {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  refine NRep.ext e (funext fun v => funext fun i => MonoidHom.ext fun s => Units.ext ?_)
  rw [← h.psi, ← h'.psi, e]

private theorem conj_mat {m : ℕ} {C : Type} [CommRing C] (h : GL (Fin m) C)
    (x : GG (m := m) (R := C)) (hx : x.right = 1) :
    (GG.ofGL h * x * (GG.ofGL h)⁻¹).left = h * x.left * h⁻¹ := by
  rw [← map_inv]
  simp [hx]

private theorem gg_map_ofGL {m : ℕ} {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin m) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := rfl

private theorem dual_mul {K : Type} [Field K] (a : DualNumber K) (c : K) :
    (TrivSqZeroExt.inr (a.fst * c) : DualNumber K) = a * TrivSqZeroExt.inr c := by
  ext <;> simp [mul_comm]

private theorem dual_fst {K : Type} [Field K] {m : ℕ} (X : Matrix (Fin m) (Fin m) K) (i j : Fin m) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) i j).fst = (1 : Matrix (Fin m) (Fin m) K) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

private theorem dual_snd {K : Type} [Field K] {m : ℕ} (X A : Matrix (Fin m) (Fin m) K) :
    ((1 + X.map (TrivSqZeroExt.inr : K → DualNumber K)) * A.map (TrivSqZeroExt.inl : K → DualNumber K)).map
      TrivSqZeroExt.snd = X * A := by
  ext i j
  rw [Matrix.add_mul, Matrix.one_mul]
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum]

theorem UpperTheory.V.Fr.pr_tor :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : NRep F n R) (B : Box F n R), ρ.Univ O → B.Of ρ → B.Cont (maximalIdeal R) → (ρ.bar O).Good → thetaLie (lieT (ResidueField O) n) = lieT (ResidueField O) n → ∃ D ∈ Tan O R, ∀ s, B.tanCo O D s = (B.bar O).ad s (lieT _ n) - lieT _ n := by
  intro l _ k _ _ F C₀ n hF O _ _ R _ _ _ ρ B hU hB hC _ hT
  haveI := (co_res O).2
  let K := ResidueField O
  let C := DualNumber K
  let μ : K →+ C := (TrivSqZeroExt.inrHom K K).toAddMonoidHom
  let ι : K →+* C := (TrivSqZeroExt.inlHom K K)
  have hμ : IsSq O μ := by
    refine ⟨fun a c => ?_, fun c => ?_⟩
    · rw [res_dual]
      exact dual_mul a c
    · rw [← res_eq_zero_iff O, res_dual]
      rfl
  have hres : (res O C : C →+* K).comp ι = RingHom.id K := RingHom.ext fun a => res_dual O _
  obtain ⟨e, e1, e2, e3, -, e5⟩ := pr_sqz O C n μ hμ
  set T := lieT K n with hTdef
  let B₀ : Box F n C := (B.bar O).map ι
  have hB₀ : B₀.bar O = B.bar O := by
    show ((B.bar O).map ι).map _ = _
    rw [Box.map_map, hres]
    rfl
  have hr₀ : ∀ s, GG.map (res O C : C →+* K) (B₀.r s) = (B.bar O).r s := fun s => by
    rw [← hB₀]; rfl
  let h := e (-T)
  have hinv : h⁻¹ = e T := by rw [e3, neg_neg]
  have hloc : ∀ s : F.G0, (B₀.r s).right = 1 := fun s => (B₀.nu s).trans s.2
  let B' : Box F n C :=
    { r := conjBy h B₀.r
      nu := fun s => by
        show (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹).right = _
        rw [← map_inv]
        simp [B₀.nu]
      g := fun v => B₀.g v * h⁻¹
      tri := fun v s => by
        have : (conjBy h B₀.r (F.loc v s)).left = h * (B₀.r (F.loc v s)).left * h⁻¹ :=
          conj_mat h _ (hloc (F.loc0 v s))
        have h2 := B₀.tri v s
        unfold GG.mat at h2 ⊢
        rw [this, ← Units.val_mul, ← Units.val_mul]
        rw [← Units.val_mul, ← Units.val_mul] at h2
        convert h2 using 2
        group }
  have hform : ∀ s, B'.r s = GG.ofGL (e ((B.bar O).ad s T - T)) * B₀.r s := fun s => by
    show GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹ = _
    rw [← map_inv, hinv, mul_assoc, e5, hr₀, ← mul_assoc, ← map_mul, ← e2, neg_add_eq_sub]
    rfl
  have hmat : ∀ s, (B'.r s).mat = (1 + ((B.bar O).ad s T - T).map μ) * ((B.bar O).r s).mat.map ι := fun s => by
    rw [hform, ← e1]
    simp [GG.mat]
    rfl
  have hbar : B.bar O |>.Of (ρ.bar O) := hB.map _
  have hc : (B'.r F.c).mat = 1 := by
    have h1 : (B.bar O).ad F.c T = T := by
      have hl : ((B.bar O).r F.c).left = 1 := Units.ext hbar.atc
      have hd : ((B.bar O).r F.c).right ≠ 1 := by
        rw [(B.bar O).nu, hF.del_c]; decide
      show ((B.bar O).r F.c).adFun T = T
      unfold GG.adFun GG.mat
      rw [hl, if_neg hd, hT]
      simp
    rw [hmat, h1, hbar.atc, sub_self, Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.map_zero _ (map_zero μ)]
    simp
  have hdiagE : ∀ a : K, ((e (a • T) : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) =
      Matrix.diagonal fun i => 1 + μ (a * (w n i : K)) := fun a => by
    rw [e1]
    ext1 i j
    by_cases hij : i = j
    · subst hij; simp [hTdef, lieT]
    · simp [hTdef, lieT, hij]
  have hd : ∀ i j, i ≠ j → ((B'.r F.g0).mat - (B'.r (F.star F.g0)).mat) i j = 0 := fun i j hij => by
    have h1 : ∀ s : F.G0, (B'.r s).mat = (h : Matrix (Fin n) (Fin n) C) * ((ρ.bar O).r s).map ι *
        ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := fun s => by
      rw [← hbar.res]
      exact congrArg Units.val (conj_mat h _ (hloc s))
    have h2 := (ρ.bar O).diag i j hij
    rw [h1, h1, ← Matrix.sub_mul, ← Matrix.mul_sub, hinv, ← one_smul K T, hdiagE, Matrix.mul_diagonal]
    have h3 : h = e ((-1 : K) • T) := by rw [neg_one_smul]
    rw [h3, hdiagE, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.map_apply, Matrix.map_apply, ← map_sub,
      ← Matrix.sub_apply, h2]
    simp
  have hcont : B'.Cont (maximalIdeal C) := fun i j N => by
    have h1 := lc_of_ker _ (pr_open hF O R B hC).1
    exact h1.comp fun x => Ideal.Quotient.mk _ ((GG.ofGL h * GG.map ι x * (GG.ofGL h)⁻¹).mat i j)
  obtain ⟨ρ', hρ', hc'⟩ := pr_ofbox hF C _ B' hc hd hcont
  have hh : GeneralLinearGroup.map (res O C : C →+* K) h = 1 := by
    apply Units.ext
    ext i j
    show res O C ((e (-T) : Matrix (Fin n) (Fin n) C) i j) = _
    rw [e1, res_dual]
    exact dual_fst _ i j
  have hB' : B'.bar O = B.bar O := by
    rw [← hB₀]
    refine Box.ext (MonoidHom.ext fun s => ?_) (funext fun v => ?_)
    · show GG.map _ (GG.ofGL h * B₀.r s * (GG.ofGL h)⁻¹) = GG.map _ (B₀.r s)
      rw [map_mul, map_mul, map_inv, gg_map_ofGL, hh]
      simp
    · show GeneralLinearGroup.map _ (B₀.g v * h⁻¹) = GeneralLinearGroup.map _ (B₀.g v)
      rw [map_mul, map_inv, hh]
      simp
  have hρb : ρ'.bar O = ρ.bar O := of_unique (hB' ▸ hρ'.map _) hbar
  obtain ⟨D, hD, hD'⟩ := pr_dof hF O R ρ B hU hB ρ' B'.r hc' hρb B'.nu hc hρ'.res
  refine ⟨D, hD, fun s => ?_⟩
  have h1 : (B'.r s).mat.map TrivSqZeroExt.snd = ((B.bar O).ad s T - T) * ((B.bar O).r s).mat := by
    rw [hmat]
    exact dual_snd _ _
  have h2 := (hD' s).symm.trans h1
  exact (Units.mul_left_inj ((B.bar O).r s).left).1 h2
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_mazur :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (H : Type) [AddCommGroup H] [Module (ResidueField O) H] [Module.Finite (ResidueField O) H], HasObs (O := O) R H → ∃ (p : MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O →ₐ[O] R) (f : Fin (Module.finrank (ResidueField O) H) → MvPowerSeries (Fin (Module.finrank (ResidueField O) (Tan O R))) O), Function.Surjective p ∧ RingHom.ker p = Ideal.span (Set.range f) := by
  intro O _ _ _ _ _ R _ _ _ H _ _ _ hob
  obtain ⟨a, π, f, hπ, hker, hcard⟩ := obs_pres O R H (by
    intro A _ _ _ p hp hK κ _ ε hspan hmin
    obtain ⟨ob, hob'⟩ := hob A p hp hK
    obtain ⟨co, hco⟩ := pr_dualb O A (RingHom.ker p) κ ε hK hspan hmin
    refine ⟨fun u => ob (co u), ?_⟩
    intro c hc A' _ _ _ p' p'' η hp' hcomp hη hη0 hε
    have hw0 : ob (∑ u, residue O (c u) • co u) = 0 := by

      rw [map_sum]
      simp only [map_smul]
      exact hc
    refine hob' _ hw0 A' p' p'' hcomp hp' ?_
    intro y hy
    obtain ⟨b, hb, hy'⟩ := hco y

    rw [hy', map_sum]
    simp only [map_smul, hε, smul_smul]
    rw [← Finset.sum_smul]
    have hm : ∑ u, b u * c u ∈ maximalIdeal O := by

      rw [← residue_eq_zero_iff, map_sum]
      simp only [map_mul, hb]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hy
      rw [← hy]
      exact Finset.sum_congr rfl (fun u _ => mul_comm _ _)
    haveI := IsCO.isLocalHom (O := O) (R := A')
    rw [Algebra.smul_def]
    exact hη _ (map_nonunit (algebraMap O A') _ hm))
  have hT := (pr_tan O R).2
  haveI := (pr_tan O R).1
  classical
  haveI := Fintype.ofFinite (ResidueField O)
  haveI : Finite (Tan O R) := Module.finite_of_finite (ResidueField O)
  haveI := Fintype.ofFinite (Tan O R)
  have h2 : 2 ≤ Fintype.card (ResidueField O) := Fintype.one_lt_card
  have hTc : Nat.card (Tan O R) =
      Fintype.card (ResidueField O) ^ Module.finrank (ResidueField O) (Tan O R) := by
    rw [Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have ha : a = Module.finrank (ResidueField O) (Tan O R) := by
    apply Nat.pow_right_injective h2
    change Fintype.card (ResidueField O) ^ a = Fintype.card (ResidueField O) ^ _
    rw [← hTc, ← hT, hcard, Nat.card_eq_fintype_card]
  subst ha
  exact ⟨π, f, hπ, hker⟩
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C C' : Type} [CommRing C] [CommRing C']

private theorem conj_left {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) :
    (conjBy h r s).left = h * (r s).left * sgnAct n C (r s).right h⁻¹ := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_assoc]

private theorem conj_right {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) :
    (conjBy h r s).right = (r s).right := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_right]

private theorem conj_mat {G : Type} [Group G] (h : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) (s : G) (hs : (r s).right = 1) :
    (conjBy h r s).mat = (h : Matrix (Fin n) (Fin n) C) * (r s).mat *
      ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
  unfold GG.mat
  rw [conj_left, hs, sgnAct_one, Units.val_mul, Units.val_mul]

private theorem conj_mul {G : Type} [Group G] (h h' : GL (Fin n) C)
    (r : G →* GG (m := n) (R := C)) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  apply MonoidHom.ext
  intro s
  simp [conjBy, MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]

private theorem frame_right_eq_one_of_G0 (B : Box F n C) (s : F.G0) : (B.r s).right = 1 := by
  exact (B.nu s).trans (MonoidHom.mem_ker.mp s.2)

private noncomputable def cj (h : GL (Fin n) C) (B : Box F n C) : Box F n C where
  r := conjBy h B.r
  nu s := (conj_right h B.r s).trans (B.nu s)
  g v := B.g v * h⁻¹
  tri v s := by
    have e : B.g v * h⁻¹ * (conjBy h B.r (F.loc v s)).left * (B.g v * h⁻¹)⁻¹ =
        B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
      have : (B.r (F.loc v s)).right = 1 := frame_right_eq_one_of_G0 B (F.loc0 v s)
      rw [conj_left, this, sgnAct_one]
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    have := B.tri v s
    unfold GG.mat at this ⊢
    rw [← e'] at this
    simpa only [Units.val_mul] using this

private theorem cj_map (f : C →+* C') (h : GL (Fin n) C) (B : Box F n C)
    (hh : (h : Matrix (Fin n) (Fin n) C).map f = 1) : (cj h B).map f = B.map f := by
  have hh' : Matrix.GeneralLinearGroup.map f h = 1 := Units.ext (by simpa using hh)
  have hg : GG.map f (GG.ofGL h) = 1 := by
    simp [GG.map, GG.ofGL, hh']
  apply Box.ext
  · apply MonoidHom.ext
    intro s
    show GG.map f (conjBy h B.r s) = GG.map f (B.r s)
    simp [conjBy, MulAut.conj_apply, map_mul, map_inv, hg]
  · funext v
    show Matrix.GeneralLinearGroup.map f (B.g v * h⁻¹) = Matrix.GeneralLinearGroup.map f (B.g v)
    simp [map_mul, map_inv, hh']

private theorem cj_cont (hd : IsOpen (F.del.ker : Set F.Γ)) (I : Ideal C) (h : GL (Fin n) C) (B : Box F n C)
    (hB : B.Cont I) : (cj h B).Cont I := by
  intro i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hdel : ∀ᶠ y in nhds x, F.del y = F.del x := by
    have hopen : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) :=
      hd.preimage (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds (by simp)] with y hy
    have e : F.del (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  have hM : ∀ᶠ y in nhds x, ∀ a b : Fin n,
      Ideal.Quotient.mk (I ^ N) ((B.r y).mat a b) = Ideal.Quotient.mk (I ^ N) ((B.r x).mat a b) := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact (hB a b N).eventually_eq x
  filter_upwards [hdel, hM] with y hy hMy
  show Ideal.Quotient.mk (I ^ N) ((conjBy h B.r y).mat i j) = Ideal.Quotient.mk (I ^ N) ((conjBy h B.r x).mat i j)
  simp only [GG.mat] at hMy ⊢

  simp only [conj_left, B.nu, hy, Units.val_mul, Matrix.mul_apply, map_sum, map_mul, hMy]

private theorem of_unique {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  apply NRep.ext e
  funext v i
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [← h.psi, ← h'.psi, e]

private theorem star_mat (hc : F.del F.c = -1) (B : Box F n C) (h1 : (B.r F.c).mat = 1) (g : F.G0) :
    (B.r (F.star g)).mat = Jmat (R := C) n * (B.r g).matᵀ * Jmat (R := C) n := by
  have t1 : theta (1 : GL (Fin n) C) = 1 := by
    simpa [sgnAct_neg_one] using map_one (sgnAct (m := n) (R := C) (-1))
  have hX : B.r F.c = ⟨1, -1⟩ := SemidirectProduct.ext (Units.ext (by simpa [GG.mat] using h1)) ((B.nu _).trans hc)
  have hY : B.r (g : F.Γ) = ⟨(B.r g).left, 1⟩ := SemidirectProduct.ext rfl (frame_right_eq_one_of_G0 B g)
  rw [show ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ from rfl, map_mul, map_mul, map_inv, map_inv, hX, hY]
  simp [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.inv_left, map_inv, sgnAct_neg_one, sgnAct_one, theta_inv_val]
  rw [t1, t1, Units.val_one, mul_one, ← Matrix.coe_units_inv, theta_inv_val]

end SlopeTestRemainingChoices

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (ρ : NRep F n C) (B' : Box F n C'), maximalIdeal C' * RingHom.ker p = ⊥ → (ρ.bar O).Good → (B'.map (p : C' →+* C)).Of ρ → B'.Cont (maximalIdeal C') → ∃ (h : GL (Fin n) C') (ρ' : NRep F n C'), (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ ρ'.map (p : C' →+* C) = ρ ∧ ρ'.Cont (maximalIdeal C') ∧ (conjBy h B'.r F.c).mat = 1 ∧ ∀ s : F.G0, (conjBy h B'.r s).mat = ρ'.r s := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p ρ B' hmk hgood hof hcont
  have hkp : RingHom.ker p ≤ maximalIdeal C' := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [← res_eq_zero_iff O C', ← res_map p x, hx, map_zero]
  have hmat : ∀ (B : Box F n C') (s : F.Γ), ((B.map (p : C' →+* C)).r s).mat = (B.r s).mat.map p := fun B s => rfl
  have hx1 : (B'.r F.c).mat.map p = 1 := by
    rw [← hmat]
    exact hof.atc
  obtain ⟨h1, hh1, hc1⟩ := pr_norm1 O C' C p n (B'.r F.c) hmk hkp hgood.two
    (by rw [← map_mul, hF.c_sq, map_one]) ((B'.nu _).trans hF.del_c) hx1
  set B1 := cj h1 B' with hB1
  have hB1c : (B1.r F.c).mat = 1 := hc1
  have hB1map : B1.map (p : C' →+* C) = B'.map (p : C' →+* C) := cj_map _ h1 B' hh1
  have hB1cont : B1.Cont (maximalIdeal C') := cj_cont hF.del_open _ h1 B' hcont
  have hstar : ∀ g : F.G0, (B1.r (F.star g)).mat =
      Jmat (R := C') n * (B1.r g).matᵀ * Jmat (R := C') n :=
    star_mat hF.del_c B1 hB1c
  set Z := (B1.r F.g0).mat - (B1.r (F.star F.g0)).mat with hZ
  have hJ : ∀ X : Matrix (Fin n) (Fin n) C', Jmat (R := C') n * (Jmat (R := C') n * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  have hθ : thetaLie Z = Z := by
    rw [hZ, hstar]
    simp only [thetaLie, Matrix.transpose_sub, Matrix.transpose_mul, Jmat_transpose, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hJ, Jmat_mul_Jmat, Matrix.mul_one]
    abel
  have hZp : Z.map p = ρ.r F.g0 - ρ.r (F.star F.g0) := by
    rw [hZ, Matrix.map_sub _ (fun a b => map_sub p a b), ← hmat, ← hmat, hB1map, hof.res, hof.res]
  have hoff : ∀ i j : Fin n, i ≠ j → p (Z i j) = 0 := by
    intro i j hij
    have e := congrFun (congrFun hZp i) j
    rw [Matrix.map_apply] at e
    rw [e]
    exact ρ.diag i j hij
  have hdist : ∀ i j : Fin n, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j) := by
    intro i j hij
    have e : ∀ a, p (Z a a) = (ρ.r F.g0 - ρ.r (F.star F.g0)) a a := fun a => by
      rw [← hZp, Matrix.map_apply]
    rw [← res_map p, ← res_map p, e i, e j]
    convert hgood.zd i j hij using 1 <;> simp [NRep.bar, NRep.map]
  obtain ⟨h2', hh2, hθ2, hdiag2⟩ := pr_norm2 O C' C p n Z hmk hkp hθ hoff hdist
  set B2 := cj h2' B1 with hB2
  have hB2c : (B2.r F.c).mat = 1 := by
    show (conjBy h2' B1.r F.c).mat = 1
    have hl : (B1.r F.c).left = 1 := Units.ext hB1c
    unfold GG.mat
    rw [conj_left, B1.nu, hF.del_c, hl, mul_one, map_inv, sgnAct_neg_one, hθ2, mul_inv_cancel, Units.val_one]
  have hB2diag : ∀ i j : Fin n, i ≠ j → ((B2.r F.g0).mat - (B2.r (F.star F.g0)).mat) i j = 0 := by
    intro i j hij
    have e1 := conj_mat h2' B1.r (F.g0 : F.Γ) (frame_right_eq_one_of_G0 B1 F.g0)
    have e2 := conj_mat h2' B1.r ((F.star F.g0 : F.G0) : F.Γ) (frame_right_eq_one_of_G0 B1 (F.star F.g0))
    show ((conjBy h2' B1.r F.g0).mat - (conjBy h2' B1.r (F.star F.g0)).mat) i j = 0
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hdiag2 i j hij
  have hB2cont : B2.Cont (maximalIdeal C') := cj_cont hF.del_open _ h2' B1 hB1cont
  obtain ⟨ρ', hof', hcont'⟩ := pr_ofbox hF C' (maximalIdeal C') B2 hB2c hB2diag hB2cont
  refine ⟨h2' * h1, ρ', ?_, ?_, hcont', ?_, ?_⟩
  · show ((h2' : Matrix (Fin n) (Fin n) C') * h1).map (p : C' →+* C) = 1
    rw [Matrix.map_mul]
    exact (congrArg₂ (· * ·) hh2 hh1).trans (Matrix.one_mul 1)
  · have e := hof'.map (p : C' →+* C)
    rw [show B2.map (p : C' →+* C) = B'.map (p : C' →+* C) from (cj_map _ h2' B1 hh2).trans hB1map] at e
    exact of_unique e hof
  · rw [conj_mul]
    exact hB2c
  · intro s
    rw [conj_mul]
    exact hof'.res s
end
