module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle502
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle482
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle505
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle178
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowRatW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle481
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle488
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle507
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle503
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BasisRowRowsMemEigensystemTypePart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle499

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.FinAtQ

section Abs

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S] [Algebra S R]

def mulSub (L : Submodule S (n → R)) (g : ℕ) : AddSubgroup L where
  carrier := {y | ∃ z : L, (y : n → R) = g • (z : n → R)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by simp [hz, hw, smul_add]⟩
  neg_mem' := by
    rintro a ⟨z, hz⟩
    exact ⟨-z, by simp [hz]⟩

def actL (L : Submodule S (n → R)) (x : GL n R) (hx : x ∈ stabGL L) : L →+ L where
  toFun y := ⟨(x : Matrix n n R) *ᵥ (y : n → R), (hx y).1 y.2⟩
  map_zero' := by ext1; simp
  map_add' a b := by ext1; simp [Matrix.mulVec_add]

theorem mulSub_le_comap (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    mulSub L g ≤ (mulSub L g).comap (actL L x hx) := by
  rintro y ⟨z, hz⟩
  refine ⟨actL L x hx z, ?_⟩
  simp only [actL, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [hz, Matrix.mulVec_smul]

def actQ (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) :
    (L ⧸ mulSub L g) →+ (L ⧸ mulSub L g) :=
  QuotientAddGroup.map _ _ (actL L x hx) (mulSub_le_comap L g x hx)

theorem actQ_mk (L : Submodule S (n → R)) (g : ℕ) (x : GL n R) (hx : x ∈ stabGL L) (y : L) :
    actQ L g x hx (y : L ⧸ mulSub L g) = ((actL L x hx y : L) : L ⧸ mulSub L g) := rfl

def rho (L : Submodule S (n → R)) (g : ℕ) (W : Subgroup (GL n R)) (hW : W ≤ stabGL L) :
    W →* AddMonoid.End (L ⧸ mulSub L g) where
  toFun x := actQ L g x (hW x.2)
  map_one' := by
    show actQ L g 1 _ = AddMonoidHom.id _
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [actQ_mk]
      congr 1
      ext1
      simp [actL]
  map_mul' a b := by
    show actQ L g (a * b : W) _ = (actQ L g a (hW a.2)).comp (actQ L g b (hW b.2))
    refine AddMonoidHom.ext fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      rw [AddMonoidHom.comp_apply, actQ_mk, actQ_mk, actQ_mk]
      congr 1
      ext1
      simp [actL, Matrix.mulVec_mulVec]

theorem finiteIndex_of_trivOn (L : Submodule S (n → R)) (g : ℕ) (hQ : Finite (L ⧸ mulSub L g))
    (H W : Subgroup (GL n R)) (hW : W ≤ stabGL L)
    (hH : ∀ x ∈ W, (∀ y ∈ L, ∃ z ∈ L, (x : Matrix n n R) *ᵥ y - y = g • z) → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  have hE : Finite (AddMonoid.End (L ⧸ mulSub L g)) :=
    Finite.of_injective (fun f : AddMonoid.End (L ⧸ mulSub L g) => (f : (L ⧸ mulSub L g) → (L ⧸ mulSub L g)))
      (fun a b h => AddMonoidHom.ext (congrFun h))
  have hU : Finite (AddMonoid.End (L ⧸ mulSub L g))ˣ := Finite.of_injective _ Units.val_injective
  have h1 : (rho L g W hW).toHomUnits.ker.FiniteIndex := Subgroup.finiteIndex_ker _
  refine Subgroup.finiteIndex_of_le (H := (rho L g W hW).toHomUnits.ker) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : rho L g W hW x = 1 := congrArg Units.val hx
  rw [Subgroup.mem_subgroupOf]
  refine hH x x.2 fun y hy => ?_
  have h2 : actQ L g x (hW x.2) ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) = ((⟨y, hy⟩ : L) : L ⧸ mulSub L g) :=
    DFunLike.congr_fun hx' _
  rw [actQ_mk, QuotientAddGroup.eq] at h2
  obtain ⟨z, hz⟩ := h2
  refine ⟨-(z : n → R), (-z).2, ?_⟩
  have hz' : -(((x : GL n R) : Matrix n n R) *ᵥ y) + y = g • (z : n → R) := by
    simpa [actL] using hz
  rw [smul_neg, ← hz', neg_add, neg_neg, sub_eq_add_neg, add_comm]

end Abs

section Fin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_quot (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Module.Finite (𝓞 E) Λ) (g : ℕ) (hg : g ≠ 0) :
    Finite (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ ⧸
      mulSub (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) g) := by
  set L := latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ with hL
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Λ)
  let m : Fin k → Fin n → E := fun i => (s i : Fin n → E)
  have hm : ∀ i, m i ∈ Λ := fun i => (s i).2
  have hgen : ∀ l ∈ Λ, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i := by
    intro l hl
    have h0 : (⟨l, hl⟩ : Λ) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 h0
    refine ⟨c, ?_⟩
    have h1 := congrArg Subtype.val hc
    rw [Submodule.coe_sum] at h1
    simpa [m] using h1.symm
  have key := fun y => PI.LPI.plGen F E (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring n k Λ m hm hgen y
  let c : v.adicCompletionIntegers F := (g : v.adicCompletionIntegers F)
  have hcz : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hc : c ≠ 0 := by
    intro h0
    have h1 : ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 0 := by rw [h0]; rfl
    simp [c, hg] at h1
  haveI : Finite (v.adicCompletionIntegers F ⧸ Ideal.span {c}) :=
    Formalism.UG.P.glint_finite_quotient_of_dvr (Formalism.UG.P.glint_finite_residueField v) _
      (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let sec : v.adicCompletionIntegers F ⧸ Ideal.span {c} → v.adicCompletionIntegers F :=
    Function.surjInv Ideal.Quotient.mk_surjective
  have hmemf : ∀ a : Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c},
      (fun j => ∑ i, m i j ⊗ₜ[F] ((sec (a i) : v.adicCompletionIntegers F) : v.adicCompletion F)) ∈ L :=
    fun a => (key _).2 ⟨fun i => (sec (a i) : v.adicCompletion F), fun i => (sec (a i)).2, rfl⟩
  let f : (Fin k → v.adicCompletionIntegers F ⧸ Ideal.span {c}) → L ⧸ mulSub L g :=
    fun a => ((⟨_, hmemf a⟩ : L) : L ⧸ mulSub L g)
  refine Finite.of_surjective f ?_
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H y =>
  obtain ⟨a, ha, hy⟩ := (key y).1 y.2
  refine ⟨fun i => Ideal.Quotient.mk _ ⟨a i, ha i⟩, ?_⟩
  have hd : ∀ i, ∃ b : v.adicCompletionIntegers F,
      (sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) = ⟨a i, ha i⟩ + b * c := by
    intro i
    have h := Function.surjInv_eq (f := Ideal.Quotient.mk (Ideal.span {c})) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _ ⟨a i, ha i⟩)
    rw [Ideal.Quotient.eq] at h
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
    exact ⟨b, by rw [hb]; ring⟩
  choose b hb using hd
  show ((⟨_, hmemf _⟩ : L) : L ⧸ mulSub L g) = (y : L ⧸ mulSub L g)
  rw [QuotientAddGroup.eq]
  refine ⟨⟨fun j => ∑ i, m i j ⊗ₜ[F] (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F),
    (key _).2 ⟨_, fun i => (-(b i)).2, rfl⟩⟩, ?_⟩
  funext j
  have e1 : ∀ i, ((sec (Ideal.Quotient.mk _ ⟨a i, ha i⟩) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      a i + g • (b i : v.adicCompletion F) := by
    intro i
    rw [hb i]
    simp [c, nsmul_eq_mul, mul_comm]
  have hneg : ∀ i, (((-(b i)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
      -((b i : v.adicCompletionIntegers F) : v.adicCompletion F) := fun i => rfl
  rw [Submodule.coe_add, Submodule.coe_neg, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, hy]
  simp only [e1, hneg, TensorProduct.tmul_add, Finset.sum_add_distrib, TensorProduct.tmul_smul,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib, Finset.smul_sum, smul_neg]
  abel

end Fin

section Gen

open Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finiteIndex_of_princ (hc : CMData F E) (S : HSpace E) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin S.rank → E)) (hΛ : Module.Finite (𝓞 E) Λ) (N : ℕ) (hN : 0 < N)
    (H W : Subgroup (GL (Fin S.rank) (E ⊗[F] v.adicCompletion F)))
    (hW : W ≤ levelVL hc.sig S.gram v Λ) (hH : ∀ x, InPrinc hc S v N Λ x → x ∈ H) :
    (H.subgroupOf W).FiniteIndex := by
  refine finiteIndex_of_trivOn _ N (finite_quot v Λ hΛ N hN.ne') H W (hW.trans inf_le_right) ?_
  intro x hx htriv
  apply hH
  refine ⟨hW hx, ?_⟩
  intro y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  exact ⟨z, hz, by rw [e, Nat.cast_smul_eq_nsmul]⟩

end Gen



theorem chartLoc_finiteIndex : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ((((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom).subgroupOf (⨆ β', ((K β').lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom)).FiniteIndex := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hle := GlobalTheory.T.chart_localGroup_le_baseLattice_level I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb
  obtain ⟨N, hN, hpr⟩ :=
    GlobalTheory.T.chart_local_group_contains_principal_congruence I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hRd hUl hchi Lb0 hLb β v hv
  have hfin : Module.Finite (𝓞 (I.rec7 l Z).host.E) Lb0 := by
    have h0 := (F u).levJ.Lb_fin
    rw [hLb] at h0
    unfold reL at h0
    refine (Module.Finite.equiv_iff (Submodule.equivMapOfInjective
      ((reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).toLinearMap.restrictScalars
        (𝓞 (I.rec7 l Z).host.E))
      (reV (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (I.rec7 l Z).host.E).injective Lb0)).mpr ?_
    exact h0
  exact finiteIndex_of_princ _ _ v Lb0 hfin N hN _ _ (iSup_le fun β' => hle β' v hv) hpr

end GlobalTheory.Mem.Col2.FinAtQ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ToricTorsionCompare

theorem units_of_pow_eq_one : ∀ (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ), 1 ≤ k →
    ∀ (τ : Multiplicative X →* Kˣ), τ ^ k = 1 → ∃ τO : Multiplicative X →* Oˣ, ∀ x, ((τO x : O) : K) = (τ x : K) := by
  intro K _ O X _ k hk τ hτ
  have hpow : ∀ x, (τ x : K) ^ k = 1 := fun x => by
    have := congrArg (fun f => ((f x : Kˣ) : K)) hτ
    simpa [MonoidHom.pow_apply] using this
  have mem : ∀ x, (τ x : K) ∈ O := fun x => by
    rcases O.mem_or_inv_mem (τ x : K) with h | h
    · exact h
    · have h1 : (τ x : K) ^ (k - 1) * (τ x : K) = 1 := by rw [← pow_succ, Nat.sub_add_cancel hk, hpow]
      have h2 : ((τ x : K)⁻¹) ^ (k - 1) = τ x := by rw [inv_pow, inv_eq_of_mul_eq_one_right h1]
      rw [← h2]; exact O.pow_mem h _
  have vi : ∀ x, (τ x : K) * (τ x⁻¹ : K) = 1 := fun x => by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  let f : Multiplicative X → Oˣ := fun x =>
    ⟨⟨τ x, mem x⟩, ⟨τ x⁻¹, mem x⁻¹⟩, Subtype.ext (vi x), Subtype.ext ((mul_comm _ _).trans (vi x))⟩
  exact ⟨MonoidHom.mk' f (fun x y => Units.ext (Subtype.ext (by simp [f]))), fun x => rfl⟩

theorem toric_torsion_eq_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') [CharZero R] [CharZero W], AdmBase R (maximalIdeal R) → AdmBase W (maximalIdeal W) →
    ∀ (g : R →+* W) (m : SABMap t' t (spMap g))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ψ : R →+* V) [IsLocalHom ψ]
    (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
    (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
    (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
    (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G) [IsMonHom j]
    (t₀ : SAB H (Sp (ResidueField V))) (m₀ : SABMap t₀ tV (spMap (residue V)))
    (h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0) (m₀' : SABMap t₀ t (spMap ((residue V).comp ψ)))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X),
    Function.Injective α → GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
    m₀'.φ = m₀.φ ≫ mV.φ →
    GlobalTheory.TorusPart.pullTorus m₀.cart j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.PELUnif.torus P h₀ m₀' →
    α.comp ψ = β.comp g → n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
      (O : ValuationSubring F) (φ : W →+* O), IsLocalHom φ →
      (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ r, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
        algebraMap (FractionRing W) F (algebraMap W (FractionRing W) (g r))) →
    ∀ (k : ℕ), IsUnit (k : R) → ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ := by
  intro E _ _ _ H R _ _ _ t P W _ _ _ t' P' _ _ hR hW g m V _ _ _ ψ _ tV mV Ω _ α β hβ tΩ n n' j _ t₀ m₀ h₀ m₀' ρ
    hα hb hc hd he hf F _ _ _ _ O φ hφ hφW hgF k hk τ τ' q q' v v' hτ'k hττ' hqy hq hq'y hq' hv hv'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk
    · exact h
  obtain ⟨s, s1, s2, s3, s4⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H R t P hR k hk1
  obtain ⟨s', s1', s2', s3', s4'⟩ := GlobalTheory.T.exists_toric_torsion_sections_uniformisation E H W t' P' hW k hk1
  obtain ⟨fR, hfR, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨fW, hfW, -⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  let ρm := AddMonoidHom.toMultiplicative ρ
  have powc : ∀ {G : Type} [CommGroup G] (f : Multiplicative P'.D.toPre.X →* G), f ^ k = 1 → (f.comp ρm) ^ k = 1 :=
    fun f hf => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, hf]; rfl
  have hτ : τ = τ'.comp ρm := MonoidHom.ext fun x => hττ' (Multiplicative.toAdd x)
  have hτk : τ ^ k = 1 := by
    rw [hτ]; exact powc τ' hτ'k
  have hv0 : v = (s F _ τ hτk).left :=
    ((hfR q v).1 hv).trans ((hfR q _).1 (s4 F _ τ hτk q rfl hqy hq)).symm
  have hv0' : v' = (s' F _ τ' hτ'k).left :=
    ((hfW q' v').1 hv').trans ((hfW q' _).1 (s4' F _ τ' hτ'k q' rfl hq'y hq')).symm

  obtain ⟨τO, hτO⟩ := units_of_pow_eq_one F O _ k hk1 τ' hτ'k
  have hτOk : τO ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Fˣ) : F)) hτ'k
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτO, this]; rfl

  let bW : ResidueField W →+* Ω := Ideal.Quotient.lift (maximalIdeal W) β hβ
  obtain ⟨Ω', _, _, σ, κ₀, hσκ⟩ : ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (σ : Ω →+* Ω')
      (κ₀ : ResidueField O →+* Ω'), σ.comp bW = κ₀.comp (ResidueField.map φ) := by
    letI := bW.toAlgebra
    letI := (ResidueField.map φ).toAlgebra
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (ResidueField W) Ω (ResidueField O))
    letI := Ideal.Quotient.field M
    let q0 : TensorProduct (ResidueField W) Ω (ResidueField O) →+* AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) :=
      (algebraMap (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M) _).comp (Ideal.Quotient.mk M)
    refine ⟨AlgebraicClosure (TensorProduct (ResidueField W) Ω (ResidueField O) ⧸ M), inferInstance, inferInstance,
      q0.comp Algebra.TensorProduct.includeLeftRingHom, q0.comp Algebra.TensorProduct.includeRight.toRingHom, ?_⟩
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact congrArg q0.comp Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
  let κ : O →+* Ω' := κ₀.comp (residue O)
  have hκ : σ.comp β = κ.comp φ := by
    ext w
    have := congrArg (fun f => f (residue W w)) hσκ
    change σ (bW (residue W w)) = κ₀ (ResidueField.map φ (residue W w)) at this
    rw [ResidueField.map_residue] at this
    exact this
  have hκloc : IsLocalHom κ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : residue O a = 0 := (residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 hna)
    have h0 : κ a = 0 := by simp only [κ, RingHom.comp_apply, this, map_zero]
    rw [h0] at ha; exact not_isUnit_zero ha

  obtain ⟨U, hU, hUloc⟩ := IsLocalRing.exists_factor_valuationRing (σ.comp α)
  let u : V →+* U := (σ.comp α).codRestrict U.toSubring hU
  have hwu : U.subtype.comp u = σ.comp α := rfl
  let τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ := (Units.map κ.toMonoidHom).comp τO
  have h'' : τ'' ^ k = 1 := by
    rw [show τ'' ^ k = (Units.map κ.toMonoidHom).comp (τO ^ k) by ext x; simp [τ'']]
    rw [hτOk]; ext; simp
  obtain ⟨τU, hτU⟩ := units_of_pow_eq_one Ω' U _ k hk1 τ'' h''
  have hτUk : τU ^ k = 1 := by
    refine MonoidHom.ext fun x => Units.ext (Subtype.ext ?_)
    have := congrArg (fun f => ((f x : Ω'ˣ) : Ω')) h''
    simp only [MonoidHom.pow_apply, MonoidHom.one_apply, Units.val_pow_eq_pow_val, Units.val_one] at this ⊢
    rw [SubmonoidClass.coe_pow, hτU, this]; rfl
  let zU : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X :=
    (GlobalTheory.splitTorusPointsEquiv _ _ _).symm
      ((Units.map (Scheme.ΓSpecIso (CommRingCat.of U)).inv.hom.toMonoidHom).comp τU)
  have hzU : ∀ χ, GlobalTheory.UU.chV zU χ = unitOn (τU (Multiplicative.ofAdd χ)) := fun χ => by
    simp only [GlobalTheory.UU.chV, zU, MulEquiv.apply_symm_apply]; rfl
  have hkU : IsUnit (k : U) := by simpa using hk.map (u.comp ψ)
  let τRU := τU.comp ρm
  have hτRU : τRU ^ k = 1 := by
    exact powc τU hτUk
  have hG1 := GlobalTheory.T.toricTorsionSection_eq_pushed_trait_point_local E H R t P k s s1 s2 s3 _ ρ V ψ tV mV j t₀ m₀ h₀ m₀' hc hd U u hUloc hkU τU τRU hτRU hτUk
    (fun χ => rfl) zU hzU
  have hG2 := GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field E H W t' P' k s' s3' R t g m V ψ tV mV Ω α β hβ tΩ n n' j hb hf Ω' σ (κ.comp φ) hκ.symm
    U u U.subtype hwu τU τ'' h'' (fun χ => (hτU χ).symm) zU hzU
  let τRΩ := τ''.comp ρm
  have hτRΩ : τRΩ ^ k = 1 := by
    exact powc τ'' h''
  have hgU : (κ.comp φ).comp g = U.subtype.comp (u.comp ψ) := by
    ext r
    have := congrArg (fun f => σ f) (RingHom.congr_fun he r)
    have h2 := RingHom.congr_fun hκ (g r)
    simp only [RingHom.comp_apply] at this h2 ⊢
    rw [← h2, ← this]; rfl
  have h8 : (s Ω' ((κ.comp φ).comp g) τRΩ hτRΩ).left = spMap U.subtype ≫ (s U (u.comp ψ) τRU hτRU).left :=
    s2 U Ω' _ _ U.subtype τRU hτRU τRΩ hτRΩ hgU (fun χ => (hτU (ρm χ)).symm)

  let τOR := τO.comp ρm
  have hτOR : τOR ^ k = 1 := by
    exact powc τO hτOk
  obtain ⟨e, he'⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk (spMap φ)) (spMap (φ.comp g)) (spMap_comp g φ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hxy : s O (φ.comp g) τOR hτOR = e (s' O φ τO hτOk) := by
    refine GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) t.G t.semi.smooth O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' κ hκloc ?_
    · rw [s1, ← map_pow, s1', map_one]
    · rw [he', ← Category.assoc, ← s2' O Ω' φ (κ.comp φ) κ τO hτOk τ'' h'' rfl (fun χ => rfl), hG2,
        ← s2 O Ω' (φ.comp g) ((κ.comp φ).comp g) κ τOR hτOR τRΩ hτRΩ rfl (fun χ => rfl), h8, hG1]
  have hOR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    ext r; simp [hgF, hφW]
  have hOW : (algebraMap (FractionRing W) F).comp (algebraMap W (FractionRing W)) = O.subtype.comp φ := by
    ext w; simp [hφW]
  rw [hv0, hv0', s2 O F _ _ O.subtype τOR hτOR τ hτk hOR (fun χ => by simp [τOR, hτ, hτO]),
    s2' O F _ _ O.subtype τO hτOk τ' hτ'k hOW (fun χ => by simp [hτO]), hxy, he', Category.assoc]

end GlobalTheory.ToricTorsionCompare
end

section

open GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem rowRatW_of_rowTest :
    (AtDat fun _ _ _ _ _ _ _ _ z => Formalism.IndefR.Rat.RowTest (z.R.toCx3 z.F)) → RowRatW :=
  by
    intro H
    have h := (StepW.of_all fun _ _ _ _ _ _ _ s => s.1 : StepW Start Pinned).trans H
    apply h.trans
    apply StepW.of_all
    intro K B f T w hK hF G Z hX Wt z a b _ c d _ _ _ _
    exact G Z hX Wt z a b c d

end GlobalTheory.Mem.LiteralAutomorphy
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange : ∀ (sc : Scale) (D : D7) (Gt : GatTies D) (c : LatCmp D) (H : Formalism.L2.Herm.Herm0 D) (F : ∀ u, Formalism.L2.Forms.Forms0 D u) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ), IsRecG sc D Gt c H F → IsRecG sc (setDiv D N h) (gatTr N h Gt) (cmpTr N h c) (DivTr.herm0S N h H) (fun u => DivTr.forms0S N h (F u)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | exact GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv | (intros; apply GlobalTheory.Mem.Top.Bl.WitTr.isRecG_setDiv <;> assumption)
end

section

namespace GlobalTheory.T

alias divisionLocalData_preserved_divisionLatticeChange := GlobalTheory.Mem.Top.Bl.WitTr.divT_setDiv

end GlobalTheory.T
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.basis_row_rows_mem_eigensystem_type_part : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (hL : Lam3 Z), (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (principalLevelFrame.isotE R.θ Y.PY (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) (levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 true))) R.e0 (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ)))).comap R.HE.e ≤ R.EEp3 (Classical.choose hL (D.what₂.ft σ)) := by
  first | exact @GlobalTheory.Mem.IsotPart.isot_part | exact GlobalTheory.Mem.IsotPart.isot_part | (intros; apply GlobalTheory.Mem.IsotPart.isot_part <;> assumption)
end
