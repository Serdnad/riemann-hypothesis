module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeLocus
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.LengthLeOfSpan
public import Formalism.LocalRingCardinality.Bundle004
public import Formalism.LocalRingCardinality.Bundle005
import Formalism.PadicSubsetSums.StableGradedCounts.Bundle003
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
public import Formalism.SharpRestriction.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.OrderOfVanishing.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.HeightCounting Alg TensorProduct

variable {D : D7} {c : CutD D}

theorem mem_Zgood {i : (cut D c).nd.Loc} {x : (cut D c).nd.X i} : x ∈ (cut D c).nd.Zgood i ↔ x.1 ∈ D.nd.Zgood i.1 := by
  classical
  exact Finset.mem_subtype

theorem eta_le (h : c.Good) (i : (cut D c).nd.Loc) : D.nd.etaLoc i.1 ≤ (cut D c).nd.etaLoc i +
    (∑ x ∈ D.nd.Zgood i.1, D.nd.mult i.1 x : ℕ) * (padicValNat (D.nd.l i.1) D.what₂.restRowsFiniteGroupCard : ℚ) := by
  classical
  obtain ⟨α, -, hα1, hα2⟩ := h.op i.1 i.2
  have hn : D.what₂.restRowsFiniteGroupCard ≠ 0 := (D.what₂.restRowsFiniteGroupCard_pos).ne'
  have hA : ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) ≠ 0 := by
    intro hz
    have h1 : ((D.what₂.restRowsFiniteGroupCard : D.what₂.LL) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h2 : D.nd.embK i.1 (D.what₂.restRowsFiniteGroupCard : D.what₂.LL) = 0 := by
      rw [map_natCast, ← map_natCast (algebraMap (D.nd.O i.1) (FractionRing (D.nd.O i.1))), hz, map_zero]
    exact h1 ((map_eq_zero_iff _ (D.nd.embK i.1).injective).mp h2)
  have hα1' : ∀ x ∈ D.nd.Zgood i.1, ∀ u ∈ heckeEig (D.nd.T i.1) (D.nd.act i.1) x,
      (LinearMap.baseChange (FractionRing (D.nd.O i.1)) α) u = ((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1) • u := by
    intro x hx u hu
    rw [hα1 x hx u hu, Int.cast_natCast, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hY : ∀ x : ↥(c.Xs i.1), x ∈ (((cut D c).nd.Zgood i : Finset ((cut D c).nd.X i)) : Set ((cut D c).nd.X i)) ↔
      (x : D.nd.X i.1) ∈ D.nd.Zgood i.1 :=
    fun x => Iff.trans Finset.mem_coe mem_Zgood
  have key := Alg.length_le (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (D.nd.Zgood i.1) _ hY α _ hA hα1' hα2
  have hfinE : Module.length (D.nd.O i.1) (D.nd.O i.1 ⧸ Ideal.span {((D.what₂.restRowsFiniteGroupCard : ℕ) : D.nd.O i.1)}) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton _ (mem_nonZeroDivisors_of_ne_zero hA))
  have hpad := GlobalTheory.CutAtGood.lenUnit_natCast_le i.1 D.what₂.restRowsFiniteGroupCard hn
  refine (Alg.lenUnit_le_add (D.nd.l i.1) _ hfinE (fun hC => absurd hC ?_) key).trans ?_
  · exact Alg.length_ne_top ((cut D c).nd.T i) ((cut D c).nd.act i) ((cut D c).nd.T_sep i) ((cut D c).nd.Zgood i)
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpad (Nat.cast_nonneg _))

theorem eta_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.Zgood i = ∅) :
    N.etaLoc i = 0 := by
  have hsum : N.eigSum i ↑(N.Zgood i) = ⊥ := by
    rw [h]
    simp [NData.eigSum]
  have hup : N.MtUp i = ⊥ := by
    simp [NData.MtUp, hsum]
  have hsub : Subsingleton (N.MtUp i) := by
    rw [hup]
    infer_instance
  have hq : Subsingleton (↥(N.MtUp i) ⧸ Submodule.comap (N.MtUp i).subtype (N.MtLow i)) := by
    infer_instance
  unfold NData.etaLoc lenUnit
  rw [Module.length_eq_zero]
  simp

theorem etaJ_le (h : c.Good) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    (D.what₂.etaJ j w : ℝ) ≤ ((cut D c).what₂.etaJ j w : ℝ) +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℝ) := by
  classical
  let F : D.nd.Loc → ℚ := fun i => if hk : c.keep i then (cut D c).nd.etaLoc (⟨i, hk⟩ : (cut D c).nd.Loc) else 0
  have hcut : (cut D c).what₂.etaJ j w = ∑ i ∈ D.nd.locs j w, F i := by
    rw [(cut D c).etaJ_tie j w h1 h2]
    show ∑ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = _
    have hF : ∀ i ∈ Finset.subtype c.keep (D.nd.locs j w), (cut D c).nd.etaLoc i = F i.1 := by
      intro i _
      simp only [F, dif_pos i.2]
    rw [Finset.sum_congr rfl hF, Finset.sum_subtype_eq_sum_filter]
    refine Finset.sum_filter_of_ne ?_
    intro i _ hne
    by_contra hk
    exact hne (dif_neg hk)
  have hD := D.etaJ_tie j w h1 h2
  have hpt : ∀ i ∈ D.nd.locs j w, D.nd.etaLoc i ≤ F i +
      (∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) * (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    intro i hi
    have hw : D.nd.w i = w := ((D.nd.locs_mem j w i).mp hi).2
    have hl : D.what₂.places.resChar w = D.nd.l i := by
      rw [← hw]
      exact D.nd.w_l i
    rw [hl]
    by_cases hk : c.keep i
    · have hb := eta_le h (⟨i, hk⟩ : (cut D c).nd.Loc)
      simp only [F, dif_pos hk]
      push_cast at hb
      exact hb
    · have hz : D.nd.Zgood i = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        exact fun hne => hk ((h.keep i).mpr hne)
      rw [eta_zero D.nd i hz]
      simp only [F, dif_neg hk, zero_add]
      positivity
  have hQ : D.what₂.etaJ j w ≤ (cut D c).what₂.etaJ j w +
      (∑ i ∈ D.nd.locs j w, ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℚ)) *
        (padicValNat (D.what₂.places.resChar w) D.what₂.restRowsFiniteGroupCard : ℚ) := by
    rw [hD, hcut, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hpt
  exact_mod_cast hQ

end UpperTheory.GalC
end
end

section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)



@[reducible] def sideTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) :
    RowSide (cut D Λ) EE := { S with }

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem downTo_tr (μ : D.what₂.Tup) (j : ℕ) : (sideTr Λ S).downTo μ j = S.downTo μ j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg (fun f => f.comp (S.io μ j)) ih

theorem iota_tr (μ : D.what₂.Tup) : (sideTr Λ S).iota μ = S.iota μ := by
  unfold RowSide.iota; rw [downTo_tr]; rfl

theorem Qsp_tr (μ : D.what₂.Tup) : (sideTr Λ S).Qsp μ = S.Qsp μ := by
  unfold RowSide.Qsp RowSide.Usp; rw [iota_tr]; rfl

theorem RRset_tr (μ : D.what₂.Tup) : (sideTr Λ S).RRset μ = S.RRset μ := by
  unfold RowSide.RRset RowSide.LamSet; rw [iota_tr]; simp only [Qsp_tr]; rfl

theorem iiStar_tr : (sideTr Λ S).iiStar = S.iiStar := by
  have key : ∀ (f f' : S.Amb D.what₂.mu0 →ₗ[ℂ] EE) (Q Q' : Submodule ℂ (S.Amb D.what₂.mu0)), f = f' → Q = Q' →
      f.domRestrict Q ∘ₗ LinearMap.adjoint (f.domRestrict Q) = f'.domRestrict Q' ∘ₗ LinearMap.adjoint (f'.domRestrict Q') := by
    rintro _ _ _ _ rfl rfl; rfl
  exact key _ _ _ _ (iota_tr Λ S _) (Qsp_tr Λ S _)

theorem kapOf_tr {n : ℕ} (ty : Fin n → D.what₂.FT) : (sideTr Λ S).kapOf ty = S.kapOf ty := by
  unfold RowSide.kapOf RowSide.kapRatio; rw [iiStar_tr]; rfl

theorem rrDef_tr (H : S.RRDef) : (sideTr Λ S).RRDef := by
  have e : (sideTr Λ S).RRset = S.RRset := funext (RRset_tr Λ S)
  unfold RowSide.RRDef; rw [e]; exact H

end Side

theorem kapSharp_tr : kapSharp (cut D Λ) = kapSharp D := kapOf_tr Λ (RowSide.sharp D) _

def ambTr {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (x : AmbForm D S) :
    AmbForm (cut D Λ) (sideTr Λ S) := { x with }

end UpperTheory.GalC
end
end

section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Alg

def descHom {O X M B : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Semiring B] [Algebra O B]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X) (z : B →ₐ[O] Module.End O M)
    (h : ∀ b (f : T), z b * act f = act f * z b) : B →ₐ[O] Module.End O (cutM T act S) where
  toFun b := desc T act S (z b) (h b)
  map_one' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_one]; rfl
  map_mul' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [Module.End.mul_apply, desc_mk, desc_mk, desc_mk, map_mul]; rfl
  map_zero' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_zero]; rfl
  map_add' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [LinearMap.add_apply, desc_mk, desc_mk, desc_mk, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  commutes' a := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

variable {D : D7} (c : CutD D)

def zCut (Q : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (S : Set (D.nd.X i)) :
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (cutM (D.nd.T i) (D.nd.act i) S) :=
  descHom (D.nd.T i) (D.nd.act i) S (Q.zO i) (Q.zO_comm i)



def pendCut (Q : PairedCharacterCondition.Pend D) : PairedCharacterCondition.Pend (cut D c) where
  lz := Q.lz
  eSer_eq := Q.eSer_eq
  eSer_LL := Q.eSer_LL
  zetaPrimitiveRoot := fun i => Q.zetaPrimitiveRoot i.1
  om := Q.om
  om_one := Q.om_one
  om_mul := Q.om_mul
  tameInertiaChar_mul_root := Q.tameInertiaChar_mul_root
  om_wild := Q.om_wild
  om_open := Q.om_open
  om_inj := Q.om_inj
  om_tg := Q.om_tg
  inertiaCharpoly_eigenvalues := Q.inertiaCharpoly_eigenvalues
  inertiaCharpoly_character := Q.inertiaCharpoly_character
  zO := fun i => zCut Q i.1 (c.Xs i.1)
  zO_comm := fun i z f => desc_comm (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) f
  zL_stable := fun i => Q.zL_stable i.1
  zO_act := fun i z x y h =>
    (congrArg (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) (Q.zO_act i.1 z x y h)).trans
      (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) _).symm
  prMt_type := fun i PI x hx => by
    obtain ⟨a, b⟩ := Q.prMt_type i.1 PI x hx
    refine ⟨fun p hp => qK_mem (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (x := p) (a p.1 (optIn_eq_some.1 hp)), fun hn => ?_⟩
    show qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.prMt i.1 x) = 0
    cases hp : D.naut.ptV i.1 PI with
    | none => rw [b hp, map_zero]
    | some p =>
      refine qK_out (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (x := p) (fun hm => ?_) (a p hp)
      have := (optIn_eq_some (S := c.Xs i.1) (x := ⟨p, hm⟩)).2 hp
      exact Option.some_ne_none _ (this.symm.trans hn)
  Par_surj := fun i x Sig h => Q.Par_surj i.1 x.1 Sig (h.imp fun _ k => ⟨optIn_eq_some.1 k.1, k.2⟩)
  kty := fun i => Q.kty i.1
  kty_spec := fun i => Q.kty_spec i.1

theorem eigSpan_cut {Q : PairedCharacterCondition.Pend D} (h : GlobalTheory.Pass.EigSpan Q) : GlobalTheory.Pass.EigSpan (pendCut c Q) := by
  intro i z x a ha u hu
  have hu' : u ∈ (heckeEig (D.nd.T i.1) (D.nd.act i.1) x.1).map (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) := by
    rw [map_eig _ _ _ (D.nd.T_sep i.1) x]; exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  have e := h i.1 z x.1 a (fun PI hP => ha PI (optIn_eq_some.2 hP)) v hv
  refine (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) v).trans ?_
  rw [e]
  have k : ∀ (b : D.nd.O i.1) (w : TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1)),
      qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (b • w) = b • qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) w := fun b w => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i.1)) b w, map_smul, algebraMap_smul]
  exact k a v

theorem compatibilityTies_eigenRestriction (h : Tie4 D) : Tie4 (cut D c) := by
  obtain ⟨a, ⟨Q, hDZ, hE⟩, b, d⟩ := h
  exact ⟨fun i => a i.1, ⟨pendCut c Q, fun i => hDZ i.1, eigSpan_cut c hE⟩, fun i => b i.1, fun i => d i.1⟩

end UpperTheory.GalC
end
end

section

noncomputable section

namespace UpperTheory.GalC

open Formalism.BasicNotions Formalism.MainNotions NumberField

variable {D : D7} (Λ : CutD D)



@[reducible] def nchTr (x : NChoice D) : NChoice (cut D Λ) := { x with }

@[reducible] def xdTr (x : ThData D) : ThData (cut D Λ) := { x with }

theorem nchTie_tr {x : NChoice D} (H : NChTie D x) : NChTie (cut D Λ) (nchTr Λ x) :=
  { H with
    twOf_eq := fun a => H.twOf_eq a.1
    twSide_eq := fun a => H.twSide_eq a.1
    Q_eq := fun a => H.Q_eq a.1
    psi_eq := H.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

theorem sLen_tr (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ) (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E))) (ψ : BlochKatoReduction.Gen.GE D.nd →* (D.ntw.Ok i k)ˣ) :
    BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 (cut D Λ)) i s k Q ψ = BlochKatoReduction.Gen.sLen (BlochKatoReduction.bk0 D) i s k Q ψ := by
  delta BlochKatoReduction.Gen.sLen BlochKatoReduction.Gen.selT BlochKatoReduction.Gen.bk BlochKatoReduction.Gen.Trep BlochKatoReduction.Gen.Tgl BlochKatoReduction.Gen.IsImgK BlochKatoReduction.Gen.IsFrac BlochKatoReduction.Gen.phiK BlochKatoReduction.Gen.chiS BlochKatoReduction.Gen.Spl BlochKatoReduction.bk0 BlochKatoReduction.Gen.PDv BlochKatoReduction.Gen.repV BlochKatoReduction.Gen.DecV BlochKatoReduction.Gen.GE
  dsimp +instances only [cut, GlobalTheory.HeightCounting.setRaw, GlobalTheory.HeightCounting.NLay0.reEta, layCut, ndCut, GlobalTheory.HeightCounting.rowsEta]
  congr 1

theorem twAt_tr {x : NChoice D} {y : ThData D} (H : LocalQuadraticParts.TWAt D x y) : LocalQuadraticParts.TWAt (cut D Λ) (nchTr Λ x) (xdTr Λ y) := by
  obtain ⟨hc, N0, S, H⟩ := H
  refine ⟨hc, N0, S, fun w hw => ⟨(H w hw).1, ?_⟩⟩
  obtain ⟨h1, h2, h3, ⟨e, h4, h4', h4''⟩, h5, h6⟩ := (H w hw).2
  exact ⟨h1, h2, h3, ⟨e, h4, h4', fun s hs => (sLen_tr Λ _ s _ _ _).trans_le (h4'' s hs)⟩, h5, h6⟩

end UpperTheory.GalC
end
end

section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField

theorem lw_ram_nonneg (D : D7) (w : D.what₂.places.Pl) : 0 ≤ SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
  refine mul_nonneg ?_ (Nat.cast_nonneg _)
  unfold SizeData₂.lwP lw
  exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

open Classical in
theorem sum_val_le {D : D7} (L : SizeData₂ D) (N : ℕ) (hN : N ≠ 0) :
    ∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) ≤ Real.log N := by
  have h1 : Real.log N = ∑ l ∈ N.primeFactors, (padicValNat l N : ℝ) * Real.log l := by
    rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hl), Nat.padicValNat_def]
  rw [h1, ← Finset.sum_filter_add_sum_filter_not _ (fun w => D.what₂.places.resChar w ∈ N.primeFactors)]
  have h0 : ∑ w ∈ (L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0)).filter
      (fun w => ¬ D.what₂.places.resChar w ∈ N.primeFactors),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * (padicValNat (D.what₂.places.resChar w) N : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    have h2 := (Finset.mem_filter.1 hw).2
    have h3 : ¬ D.what₂.places.resChar w ∣ N := fun h =>
      h2 (Nat.mem_primeFactors.2 ⟨D.what₂.places.resChar_prime w, h, hN⟩)
    rw [Nat.padicValNat_def, multiplicity_eq_zero_of_not_dvd h3]; simp
  rw [h0, add_zero, ← Finset.sum_fiberwise_of_maps_to (g := fun w => D.what₂.places.resChar w) (t := N.primeFactors)
    (fun w hw => (Finset.mem_filter.1 hw).2)]
  refine Finset.sum_le_sum fun l hl => ?_
  have hm := TwistedPlaces.admissibleMeanCondition_holds L l (Nat.prime_of_mem_primeFactors hl)
  calc _ = (padicValNat l N : ℝ) * ∑ w ∈ TwistedPlaces.twAt L l, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr ?_ fun w hw => ?_
        · ext w
          simp only [Finset.mem_filter, TwistedPlaces.mem_twAt, TwistedPlaces.TwPl]
          constructor
          · rintro ⟨⟨⟨a, b⟩, -⟩, e⟩; exact ⟨a, b, e⟩
          · rintro ⟨a, b, e⟩; exact ⟨⟨⟨a, b⟩, e ▸ hl⟩, e⟩
        · rw [(TwistedPlaces.mem_twAt.1 hw).2.2]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)

open Classical in
theorem etaSum_le_add {D : D7} (L : SizeData₂ D) (j : ℕ) (η : D.what₂.places.Pl → ℝ) (d : ℝ) (hd : 0 ≤ d) (N : ℕ) (hN : N ≠ 0)
    (h : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      (D.what₂.etaJ j w : ℝ) ≤ η w + d * (padicValNat (D.what₂.places.resChar w) N : ℝ)) :
    Formalism.MainNotions.etaSum L j ≤ (∑ w ∈ L.supp.filter (fun w => D.what₂.muAt w ≠ D.what₂.mu0),
      SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) * η w) + d * Real.log N := by
  refine le_trans ?_ (add_le_add_right (mul_le_mul_of_nonneg_left (sum_val_le L N hN) hd) _)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have := mul_le_mul_of_nonneg_left (h w (Finset.mem_filter.1 hw).2) (lw_ram_nonneg D w)
  linarith

theorem ev_pow_le_exp (C eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ x ≥ x0, x ^ C ≤ Real.exp (x ^ eps) ∧ 1 ≤ x ^ eps := by
  have h2 := ((isLittleO_log_rpow_atTop he).const_mul_left C).bound one_pos
  obtain ⟨x0, h⟩ := Filter.eventually_atTop.1 (h2.and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨a, b⟩ := h x hx
  have x0' : 0 < x := by linarith
  refine ⟨?_, Real.one_le_rpow b he.le⟩
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg x0'.le _), Real.norm_eq_abs] at a
  rw [Real.rpow_def_of_pos x0', mul_comm]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans a)

end UpperTheory.GalC
end
end
