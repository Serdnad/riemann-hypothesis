module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
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
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.LRank


open scoped TensorProduct in
theorem natCard_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

theorem finrank_of_card {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {n : ℕ}
    (h : Nat.card V = Nat.card F ^ n) : Module.finrank F V = n := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite F V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := F) (V := V)
  rw [h] at h2
  exact (Nat.pow_right_injective h1 h2).symm



theorem finrank_red {E : Type} [Field E] [NumberField E] {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (P : HeightOneSpectrum (𝓞 E)) :
    Module.finrank (Res P) (TDat.Red N P) = n := by
  let : Submodule.IsFullLattice E N := hN
  have : Module.Finite (𝓞 E) N := Submodule.IsLattice.finite E N
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    exact (Submodule.IsFullLattice.finrank_eq E N).trans (Module.finrank_fin_fun E)
  have h := natCard_quot (R := 𝓞 E) (N := N) P.asIdeal
  rw [hr] at h
  exact finrank_of_card (F := Res P) h



theorem ranks : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  intro E K _ _ _ _ n S ST A T _ h
  exact ⟨fun P c => finrank_red _ (h.N_lat c.1 (S.rep c)) P.1,
    fun P c => finrank_red _ (h.dnN_lat c.1 (S.rep c) P) P.1⟩

end GlobalTheory.Mem.Col2.LRank
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaRep

set_option linter.unusedSectionVars false

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem trFr_mul_apply (γ δ : GL (Fin n) E) (c d : Kˣ) (F : Fr emb σ n → ℂ) :
    trFr emb σ (γ * δ) (c * d) F = trFr emb σ γ c (trFr emb σ δ d F) := by
  funext y
  simp only [trFr_apply, mul_inv_rev, frMul_mul, Units.val_mul, map_mul, mul_assoc]

theorem trFr_one_apply (F : Fr emb σ n → ℂ) : trFr emb σ (1 : GL (Fin n) E) (1 : Kˣ) F = F := by
  funext y
  simp only [trFr_apply, inv_one, frMul_one, Units.val_one, map_one, one_mul]

theorem tr_mul_apply (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  unfold GStep.tr
  rw [map_mul, map_mul, trFr_mul_apply]

theorem tr_one_apply (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  unfold GStep.tr
  rw [map_one, map_one, trFr_one_apply]

theorem mk_smul (b : S.β) (g : S.G b) (d : S.D b) :
    Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) (g • d) = Quotient.mk _ d :=
  Quotient.sound ⟨g, rfl⟩

theorem mv_smul' (b : S.β) (d : S.D b) : S.mv b d • S.rp b (Quotient.mk _ d) = d := S.mv_smul b d

theorem eq_of_free (hf : S.Free) (b : S.β) (g h : S.G b) (d : S.D b) (e : g • d = h • d) : g = h := by
  have h1 : (h⁻¹ * g) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 := hf b _ d h1
  exact (inv_mul_eq_one.1 h2).symm

theorem mv_smul_eq (hf : S.Free) (b : S.β) (g : S.G b) (d : S.D b) : S.mv b (g • d) = g * S.mv b d := by
  apply eq_of_free S hf b _ _ (S.rp b (Quotient.mk _ d))
  have h1 := mv_smul' S b (g • d)
  rw [mk_smul] at h1
  rw [h1, mul_smul, mv_smul']

theorem mv_rp (hf : S.Free) (b : S.β) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.mv b (S.rp b q) = 1 := by
  apply hf b _ (S.rp b q)
  have h1 := mv_smul' S b (S.rp b q)
  rwa [S.rp_spec] at h1

def evPt (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b) : Fr emb σ n → ℂ :=
  S.tr emb σ b (S.mv b d) (φ ⟨b, Quotient.mk _ d⟩)

theorem evPt_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    evPt S emb σ φ b (g • d) = S.tr emb σ b g (evPt S emb σ φ b d) := by
  unfold evPt
  rw [mv_smul_eq S hf, tr_mul_apply, mk_smul]

theorem evPt_rep (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) :
    evPt S emb σ φ c.1 (S.rep c) = φ c := by
  obtain ⟨b, q⟩ := c
  show S.tr emb σ b (S.mv b (S.rp b q)) (φ ⟨b, Quotient.mk _ (S.rp b q)⟩) = φ ⟨b, q⟩
  rw [mv_rp S hf, tr_one_apply, S.rp_spec]

end Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem diaLin_apply (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) (c : (I.S 0).Cl) :
    J.diaLin emb σ P a φ c = evPt (I.S 0) emb σ φ c.1 ((J.A 0).dia c.1 P a ((I.S 0).rep c)) := rfl

theorem evPt_diaLin (h : J.Ok) (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ)
    (b : (I.S 0).β) (d : (I.S 0).D b) :
    evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a d) := by
  have h1 : evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = (I.S 0).tr emb σ b ((I.S 0).mv b d)
      (evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a ((I.S 0).rp b (Quotient.mk _ d)))) := rfl
  rw [h1, ← evPt_smul _ _ _ h.free0, ← (h.lev 0).dia_act, mv_smul']

theorem lawDiaOne (h : J.Ok) : J.LawDiaOne emb σ := by
  intro P
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [diaLin_apply, (h.lev 0).dia_one, evPt_rep _ _ _ h.free0]
  rfl

theorem lawDiaMul (h : J.Ok) : J.LawDiaMul emb σ := by
  intro P a b
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [Module.End.mul_apply, diaLin_apply, diaLin_apply, evPt_diaLin J emb σ h, ← (h.lev 0).dia_mul, mul_comm b a]

theorem diamond_rep : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ :=
  fun _ J emb σ _ _ _ h => ⟨lawDiaOne J emb σ h, lawDiaMul J emb σ h⟩

end GlobalTheory.Mem.Col2.DiaRep
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.TDat

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) {T : ℕ}

theorem exists_fv (h : A.Ok T) (P : ST) (c : S.Cl) :
    ∃ φ : Module.Dual (Res P.1) (A.lv P c), ∀ x : A.N c.1 (S.rep c),
      φ (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  let g : A.N c.1 (S.rep c) →ₗ[𝓞 E] Res P.1 :=
    { toFun := fun x => A.f c.1 (S.rep c) P x
      map_add' := fun x y => h.f_add _ _ _ _ x.2 _ y.2
      map_smul' := fun a x => by
        have := h.f_smul _ _ P a _ x.2
        simp only [RingHom.id_apply]
        rw [Submodule.coe_smul, this]
        rfl }
  have hk : P.1.asIdeal • (⊤ : Submodule (𝓞 E) (A.N c.1 (S.rep c))) ≤ LinearMap.ker g := by
    refine Submodule.smul_le.2 fun a ha x _ => ?_
    rw [LinearMap.mem_ker, map_smul]
    show Ideal.Quotient.mk P.1.asIdeal a * g x = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  let g' : A.lv P c →ₗ[𝓞 E] Res P.1 := Submodule.liftQ _ g hk
  refine ⟨{ toFun := g', map_add' := g'.map_add, map_smul' := ?_ }, fun x => rfl⟩
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  exact g'.map_smul a x

theorem fv_mk (h : A.Ok T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have hx := A.exists_fv h P c
  unfold fv
  rw [dite_eq_left hx]
  exact hx.choose_spec x

theorem fv_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.fv P c ≠ 0 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne c.1 (S.rep c) P
  intro h0
  have := A.fv_mk h P c ⟨x, hx⟩
  rw [h0] at this
  exact hne this.symm

theorem exists_f_eq_one (h : A.Ok T) (b : S.β) (d : S.D b) (P : ST) : ∃ e ∈ A.N b d, A.f b d P e = 1 := by
  obtain ⟨x, hx, hne⟩ := h.f_ne b d P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (A.f b d P x)⁻¹
  refine ⟨a • x, (A.N b d).smul_mem a hx, ?_⟩
  rw [h.f_smul b d P a x hx, ha]
  exact inv_mul_cancel₀ hne

theorem te_ne_zero (h : A.Ok T) (P : ST) (c : S.Cl) : A.te T P c ≠ 0 := by
  have hx : ∃ t : A.dnN c.1 (S.rep c) P, ∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧
      (t : Fin n → E) = (T : 𝓞 E) • e := by
    obtain ⟨e, he, h1⟩ := A.exists_f_eq_one h c.1 (S.rep c) P
    exact ⟨⟨_, (h.te_mem _ _ P e he h1).1⟩, e, he, h1, rfl⟩
  unfold te
  rw [dite_eq_left hx]
  obtain ⟨e, he, h1, ht⟩ := hx.choose_spec
  intro h0
  rw [Submodule.Quotient.mk_eq_zero] at h0
  apply (h.te_mem _ _ P e he h1).2
  rw [← ht]
  have := Submodule.mem_map_of_mem (f := (A.dnN c.1 (S.rep c) P).subtype) h0
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at this
  exact this

end GlobalTheory.Mem.Col2.TDat

namespace GlobalTheory.Mem.Col2

theorem fv_te_laws : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c (x : A.N c.1 (S.rep c)), A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x) ∧
    (∀ P c, A.fv P c ≠ 0) ∧ ∀ P c, A.te T P c ≠ 0 :=
  fun A _ _ h => ⟨A.fv_mk h, A.fv_ne_zero h, A.te_ne_zero h⟩

end GlobalTheory.Mem.Col2
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TilX

section Ext

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

def extM (_hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A) : Matrix (Fin N) (Fin N) A := fun a b =>
  if ha : a.1 < n then (if hb : b.1 < n then g ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else if b.1 < n then 0 else 1

theorem extM_castSucc (g : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc j.castSucc = g i j := by
  simp [extM]

theorem extM_castSucc_last (g : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc (Fin.last n) = 0 := by
  simp [extM]

theorem extM_last_castSucc (g : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) j.castSucc = 0 := by
  simp [extM]

theorem extM_last_last (g : Matrix (Fin n) (Fin n) A) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

theorem extM_mulVec_iC (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) (i : Fin n) :
    (extM hN g *ᵥ x) (Br.iC hN i) = (g *ᵥ iniH hN x) i := by
  subst hN
  have e : Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_castSucc, extM_castSucc_last, zero_mul, add_zero]
  rfl

theorem extM_mulVec_iL (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    (extM hN g *ᵥ x) (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  have e : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_last_castSucc, extM_last_last, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]

theorem extM_one : extM hN (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · rw [extM_castSucc, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]

theorem extM_mul (g h : Matrix (Fin n) (Fin n) A) : extM hN (g * h) = extM hN g * extM hN h := by
  subst hN
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_castSucc_last]
  · simp [extM_castSucc, extM_castSucc_last, Matrix.mul_apply]

def extGL : GL (Fin n) A →* GL (Fin N) A :=
  Units.map { toFun := extM hN, map_one' := extM_one hN, map_mul' := extM_mul hN }

theorem extGL_val (g : GL (Fin n) A) : (extGL hN g : Matrix (Fin N) (Fin N) A) = extM hN g := rfl

theorem extGL_inv_val (g : GL (Fin n) A) :
    ((extGL hN g)⁻¹ : GL (Fin N) A).1 = extM hN ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  rw [← map_inv, extGL_val]

theorem eq_extM {M : Matrix (Fin N) (Fin N) A} {g : Matrix (Fin n) (Fin n) A}
    (h1 : ∀ (a : Fin N) (j : Fin n), M a (Br.iC hN j) = extM hN g a (Br.iC hN j))
    (h2 : ∀ a : Fin N, M a (Br.iL hN) = extM hN g a (Br.iL hN)) : M = extM hN g := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) b
  · exact h2 a
  · exact h1 a j

end Ext

end GlobalTheory.Mem.Col2.TilX

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaCl

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem cl_smul_eq (b : S.β) (g : S.G b) (d : S.D b) : S.cl b (g • d) = S.cl b d :=
  congrArg (Sigma.mk b) (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • d) d from ⟨g, rfl⟩))

theorem cl_rep_eq (c : S.Cl) : S.cl c.1 (S.rep c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) (S.rp_spec b q)

theorem exists_move (b : S.β) (d : S.D b) : ∃ g : S.G b, g • S.rep (S.cl b d) = d :=
  (MulAction.orbitRel (S.G b) (S.D b)).symm (Quotient.exact (S.rp_spec b (Quotient.mk _ d)))

theorem dia_inj (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) : Function.Injective (A.dia b P a) := by
  intro d d' hd
  have := congrArg (A.dia b P a⁻¹) hd
  rwa [← h.dia_mul, ← h.dia_mul, inv_mul_cancel, h.dia_one, h.dia_one] at this

theorem stab_dia (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) (d : S.D b) :
    MulAction.stabilizer (S.G b) (A.dia b P a d) = MulAction.stabilizer (S.G b) d := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← h.dia_act]
  exact (dia_inj h b P a).eq_iff

theorem card_stab_cl (b : S.β) (d : S.D b) :
    Nat.card (S.Stab (S.cl b d)) = Nat.card (MulAction.stabilizer (S.G b) d) := by
  obtain ⟨g, hg⟩ := exists_move (S := S) b d
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv

end GlobalTheory.Mem.Col2.DiaCl

namespace GlobalTheory.Mem.Col2

open DiaCl

theorem diamond_action_on_classes : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧
    (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧
    ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  intro E K _ _ _ _ n S ST A T _ h
  refine ⟨fun P c => ?_, fun P a b c => ?_, fun P a c => ?_⟩
  · unfold TDat.diaPt
    rw [h.dia_one, cl_rep_eq]
  · unfold TDat.diaPt
    obtain ⟨g, hg⟩ := exists_move (S := S) c.1 (A.dia c.1 P b (S.rep c))
    rw [← cl_smul_eq c.1 g (A.dia c.1 P a _), ← h.dia_act, hg, h.dia_mul]
  · rw [card_stab_cl]
    unfold TDat.diaPt
    rw [stab_dia h]

end GlobalTheory.Mem.Col2
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

namespace GlobalTheory.OscGauss

theorem continuous_matrix_inv_of_isUnit_det {T n : Type} [TopologicalSpace T] [Fintype n] [DecidableEq n]
    {M : T → Matrix n n ℂ} (hM : Continuous M) (h : ∀ t, IsUnit (M t).det) : Continuous fun t => (M t)⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hM.matrix_det.inv₀ fun t => (h t).ne_zero).smul hM.matrix_adjugate

theorem continuous_ker_right (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ)
    (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ) (hY : Continuous Y')
    (hv : Continuous v') (hφ : Continuous φ') (h : ∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) :
    Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  have hM : Continuous fun t => Yᴴ * Jm P Q * Y' t := continuous_const.matrix_mul hY
  have hI := continuous_matrix_inv_of_isUnit_det hM h
  unfold ker
  refine (hM.neg.matrix_det.inv₀ fun t => ?_).mul (Complex.continuous_exp.comp (Continuous.sub
    (continuous_const.dotProduct hv) ((continuous_const.add hφ).dotProduct
      ((((hY.matrix_mul hI).matrix_mul continuous_const).matrix_mul continuous_const).matrix_mulVec
        (continuous_const.add hv)))))
  rw [Pi.neg_apply, Matrix.det_neg]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (h t).ne_zero

end GlobalTheory.OscGauss
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  first | exact @GlobalTheory.unitary_offRow_stab_three | exact GlobalTheory.unitary_offRow_stab_three | (intros; apply GlobalTheory.unitary_offRow_stab_three <;> assumption)
end
